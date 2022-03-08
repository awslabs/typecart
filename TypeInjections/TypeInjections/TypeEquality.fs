// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT

namespace TypeInjections

open System.IO
open Microsoft.Dafny
open System.Collections.Generic
open NameUtils
open Utils

// Before generating injections, we want to determine which types are equal and which are not. This module
// contains that logic.
module TypeEquality =

    // We want to memoize the computation so that we don't need to compute the result multiple times if a type is
    // referenced in other types. Using mutable state is cleaner than passing around sets everywhere
    let same : HashSet<string> = HashSet<string>()
    let diff : HashSet<string> = HashSet<string>()

    // Stores the decls for each type that we know is equal, since we will need to reference these decls later
    let oldDecls : Dictionary<string, TopLevelDecl> = Dictionary<string, TopLevelDecl>()
    let newDecls : Dictionary<string, TopLevelDecl> = Dictionary<string, TopLevelDecl>()

    let fieldsOf (c: ClassDecl) : Field list =
        List.choose
            (fun (m: MemberDecl) ->
                match m with
                // Field includes ConstantField, DatatypeDestructor, SpecialField
                | :? Field as f -> Some f
                | _ -> None)
            (fromList c.Members)

    let ctrOf (c: ClassDecl) : Constructor option =
        let constructors (c: ClassDecl) : Constructor list =
            List.choose
                (fun (m: MemberDecl) ->
                    match m with
                    | :? Constructor as m -> Some m
                    | _ -> None)
                (fromList c.Members)

        if (constructors c).Length = 1 then
            Some (constructors c).Head
        else
            None

    let rec dropInitConsts (fs: Field list) : Field list =
        match fs with
        | [] -> []
        | x :: xs ->
            match x with
            | :? ConstantField as c ->
                if c.Rhs = null then
                    x :: dropInitConsts xs
                else
                    dropInitConsts xs
            | _ -> x :: dropInitConsts xs

    let rec constFields (fs: Field list) : ConstantField list =
        match fs with
        | [] -> []
        | x :: xs ->
            match x with
            | :? ConstantField as c -> c :: constFields xs
            | _ -> constFields xs

    let rec initConsts (cs: ConstantField list) : ConstantField list =
        match cs with
        | [] -> []
        | x :: xs ->
            if x.Rhs = null then
                initConsts xs
            else
                x :: initConsts xs

    // syntactic check for class constructors
    // we strictly require classes to follow this structure:
    // class A {
    //   var x: foo
    //   const y:int
    //   const z := 3
    //   constructor (x:foo, y:int)
    //     ensures this.x == x
    //     ensures this.y == y
    //   {
    //     this.x := x;
    //     this.y := y;
    //   }
    // }
    let synCheckClass (c: ClassDecl) : bool =
        let argCheck (fields: Field list) (args: Formal list) : bool =
            let cs = initConsts (constFields fields)

            let fs =
                dropInitConsts fields
                |> List.sortBy (fun x -> x.Name)

            let ins = args |> List.sortBy (fun x -> x.Name)

            // for the time being, we require that class fields and constructor arguments have same names,
            // why: for efficient implementation
            let rec checkNames (fs: Field list) (ins: Formal list) : bool =
                match fs, ins with
                | [], [] -> true
                | x :: xs, y :: ys ->

                    let xTypeName =
                        x.Type.TypeName(c.EnclosingModuleDefinition, true)

                    let yTypeName =
                        y.Type.TypeName(c.EnclosingModuleDefinition, true)

                    x.Name = y.Name
                    // since we deal with parsed files, it is sufficient to check only type names here
                    && xTypeName = yTypeName
                    && checkNames xs ys
                | _ -> failwith "unreachable"

            fields.Length - cs.Length = ins.Length
            && checkNames fs ins

        let ensCheck (c: Constructor) (fs: Field list) : bool =
            let ensureMap : Dictionary<string, MemberDecl> = Dictionary<string, MemberDecl>()

            let expMap (e: Expression) : unit =
                match e with
                | :? BinaryExpr as b ->
                    match (b.E0.Resolved, b.E1.Resolved) with
                    | :? MemberSelectExpr as m, (:? IdentifierExpr as n) ->
                        match m.Obj with
                        | :? ThisExpr -> updateDict ensureMap n.Name m.Member
                        | _ -> ()
                    | _ -> ()
                | _ -> ()

            let ensExps = c.Ens |> fromList

            List.map (fun (e: AttributedExpression) -> expMap e.E) ensExps
            |> ignore

            ensExps.Length = (dropInitConsts fs).Length
            && List.fold
                (fun b (f: Field) ->
                    b
                    && if ensureMap.ContainsKey f.Name then
                           ensureMap.[f.Name] = (f :> MemberDecl)
                       else
                           false)
                true
                (dropInitConsts fs)

        let bodyCheck (c: Constructor) (fs: Field list) : bool =
            let stmtMap : Dictionary<string, MemberDecl> = Dictionary<string, MemberDecl>()

            let expMap (st: Statement) : unit =
                match st with
                | :? UpdateStmt as u ->
                    let sts = u.ResolvedStatements |> fromList

                    if sts.Length = 1 then
                        match sts.Head with
                        | :? AssignStmt as ast ->
                            match (ast.Lhs, ast.Rhs) with
                            | :? MemberSelectExpr as m, (:? ExprRhs as n) ->
                                match n.Expr with
                                | :? NameSegment as exp -> updateDict stmtMap exp.Name m.Member
                                | _ -> ()
                            | _ -> ()
                        | _ -> ()
                    else
                        ()
                | _ -> ()

            let stmts = c.Body.Body |> fromList

            List.map (fun (stmt: Statement) -> expMap stmt) stmts
            |> ignore

            stmts.Length = (dropInitConsts fs).Length
            && List.fold (fun b (f: Field) -> b && stmtMap.ContainsKey f.Name) true (dropInitConsts fs)

        let fields = fieldsOf c
        let ctr = ctrOf c

        if Option.isNone ctr then
            false
        else
            let ctr = Option.get ctr
            let ins = ctr.Ins |> fromList

            argCheck fields ins
            && ensCheck ctr fields
            && bodyCheck ctr fields

    // Given two same-length lists of TypeParameters, construct a mapping from one to the other
    // This allows us to deal with types that change the names of generic arguments, as long as the order is preserved
    let rec private typeArgMap (l1: TypeParameter list) (l2: TypeParameter list) : Map<string, string> =
        List.fold2 (fun m (x: TypeParameter) (y: TypeParameter) -> Map.add x.Name y.Name m) Map.empty l1 l2

    // Check the equality of the expressions for newtypes. This is a syntactic equivalence check, so two expressions
    // may be logically equivalent but be marked as inequivalent. This supports equalities and inequalities (including
    // compound inequalities) and boolean operators.
    // "names" denotes the names of the two variables (ie: x in type foo = x | p(x)). We take in both names, since
    // we allow the two newtypes to use different variable names, as long as the use is consistent.
    let rec private exprEq (names: (string * string) option) (e1: Expression) (e2: Expression) : bool =
        match (e1, e2) with
        | :? ChainingExpression as c1, (:? ChainingExpression as c2) -> exprEq names c1.E c2.E
        | :? BinaryExpr as b1, (:? BinaryExpr as b2) ->
            b1.Op = b2.Op
            && exprEq names b1.E0 b2.E0
            && exprEq names b1.E1 b2.E1
        | :? LiteralExpr as l1, (:? LiteralExpr as l2) -> l1.Value = l2.Value
        | :? NameSegment as n1, (:? NameSegment as n2) ->
            (match names with
             | Some names -> n1.Name = fst names && n2.Name = snd names
             | None -> false)
            || n1.Name = n2.Name
        // NOTE: the above assumes that constants with the same name are equivalent. This is unsafe, but storing
        // the values of all given constants is a bit complicated, so we use this approximation for now.
        | :? NegationExpression as n1, (:? NegationExpression as n2) -> exprEq names n1.E n2.E
        | _, _ ->
            System.Console.WriteLine("Newtype expressions limited to \"a <= x < b\" and similar")
            false

    // The equality computation consists of several mutually recursive functions. The "update_" functions are the
    // top level functions for each type decl (ie: DatatypeDecl, NewtypeDecl, etc), and they update the above maps as well.

    // The core function that checks for type equivalence, subject to the given typeArgs map between generic parameters.
    // currTypeName is the name of the two types (equality of names is checked before calling this function) and is used
    // for recursive types.
    // NOTE: this results in a stack overflow on mutually recursive types. It is difficult to fix this without degrading
    // performance
    let rec private typeEq (currTypeName: string) (typeArgs: Map<string, string>) (t1: Type) (t2: Type) : bool =
        match t1, t2 with
        // For the most part, the interesting cases are the UserDefinedTypes
        | :? UserDefinedType as u1, (:? UserDefinedType as u2) ->
            match u1.ResolvedClass, u2.ResolvedClass with
            | :? TypeParameter as p1, (:? TypeParameter as p2) ->
                typeArgs.ContainsKey(p1.Name)
                && typeArgs.[p1.Name] = p2.Name
            | :? SubsetTypeDecl as s1, (:? SubsetTypeDecl as s2) ->
                if s1.Name = "nat" && s2.Name = "nat" then
                    true
                else
                    updateTypeSynonymEq s1 s2
            | :? TypeSynonymDecl as t1, (:? TypeSynonymDecl as t2) ->
                // not all Type Synonyms should be stored, so we just compare the inner type
                typeEq currTypeName typeArgs t1.Rhs t2.Rhs
            | :? DatatypeDecl as dd1, (:? DatatypeDecl as dd2) ->
                (currTypeName = typeName dd1
                 && currTypeName = typeName dd2) // for recursive datatypes
                || (updateDataTypeEq dd1 dd2 //for references to other user-defined datatypes
                    && forallSafe (typeEq currTypeName typeArgs) (fromList t1.TypeArgs) (fromList t2.TypeArgs))
            // in case the user-defined type has arguments, we must check that those arguments agree as well
            | :? ClassDecl as c1, (:? ClassDecl as c2) ->
                (currTypeName = typeName c1
                 && currTypeName = typeName c2) // for classes that refer to themselves
                || updateClassTypeEq c1 c2
            | :? NewtypeDecl as n1, (:? NewtypeDecl as n2) -> updateNewTypeEq n1 n2
            // Dafny considers type synonyms to be equal with their base type; so do we
            | :? TypeSynonymDecl as t1, _ -> typeEq currTypeName typeArgs t1.Rhs t2
            | _, (:? TypeSynonymDecl as t2) -> typeEq currTypeName typeArgs t1 t2.Rhs
            | _, _ -> false
        // We also need to check type synonyms with their base types here
        | :? UserDefinedType as u1, _ ->
            // check here for `nat`, that is a predefined TypeSyn for int
            // its enough to check for "nat" names here as we will reach to this case only when one of the type is `UserDefinedType`
            // and the other is not
            if u1.Name = "nat" then
                match t2 with
                | :? UserDefinedType as u2 -> u2.Name = "nat"
                | _ -> false
            else
                let syn = u1.AsTypeSynonym

                not (syn = null)
                && typeEq currTypeName typeArgs syn.Rhs t2
        | _, (:? UserDefinedType as u2) ->
            // check here for `nat`, that is a predefined TypeSyn for int
            if u2.Name = "nat" then
                match t1 with
                | :? UserDefinedType as u2 -> u2.Name = "nat"
                | _ -> false
            else
                let syn = u2.AsTypeSynonym

                not (syn = null)
                && typeEq currTypeName typeArgs t1 syn.Rhs
        | :? SeqType as s1, (:? SeqType as s2) -> typeEq currTypeName typeArgs s1.Arg s2.Arg
        | :? SetType as s1, (:? SetType as s2) -> typeEq currTypeName typeArgs s1.Arg s2.Arg
        | :? MapType as m1, (:? MapType as m2) ->
            (typeEq currTypeName typeArgs m1.Domain m2.Domain)
            && (typeEq currTypeName typeArgs m1.Range m2.Range)
        | :? CharType, :? CharType -> true
        | :? IntType, :? IntType -> true
        | :? RealType, :? RealType -> true
        | :? BoolType, :? BoolType -> true
        | :? BitvectorType as bv1, (:? BitvectorType as bv2) -> bv1.Width = bv2.Width
        // For now, only consider inferred integers to be equal
        | :? InferredTypeProxy as i1, (:? InferredTypeProxy as i2) -> (i1.IsIntegerType && i2.IsIntegerType)
        | _, _ ->
            let msg : string = t1.ToString() + " not supported" in

            t1 = t2
            || ((if t1.ToString() = t2.ToString() then
                     System.Console.WriteLine(msg))

                false)

    // Determine if two DatatypeDecls are equivalent and update "same" and "diff" accordingly.
    // Two DatatypeDecls are equivalent if they have the same name, consistent generic arguments, and their constructors
    // are permutations of each other.
    and private updateDataTypeEq (d1: DatatypeDecl) (d2: DatatypeDecl) : bool =
        // We short circuit if we can easily tell that the types are equal or not.
        // This occurs if the names are different or if we find the names in one of the two known sets.
        let fstName = typeName d1
        let sndName = typeName d2
        let sameName = fstName = sndName

        let res =
            sameName
            && not (diff.Contains(fstName))
            && (same.Contains(fstName)
                || (d1.TypeArgs.Count = d2.TypeArgs.Count
                    &&
                    // sort constructor lists - the constructors are allowed to be reordered
                    forallSafe
                        (datatypeCtorEq (typeArgMap (fromList d1.TypeArgs) (fromList d2.TypeArgs)))
                        (List.sortBy (fun x -> x.Name) (fromList d1.Ctors))
                        (List.sortBy (fun x -> x.Name) (fromList d2.Ctors))))

        let setToAdd = if res then same else diff
        // Only update maps for types with the same name (otherwise, we may introduce false negatives - for instance,
        // we may have List<Foo> and List<Bar>, but Foo and Bar should not necessarily be marked as inequivalent to
        // their corresponding decls)
        (if sameName then
             ignore (setToAdd.Add(fstName))
             updateDict oldDecls fstName (d1 :> TopLevelDecl)
             updateDict newDecls sndName (d2 :> TopLevelDecl))

        res

    // Two datatype constructors are equivalent if they have the same name and all of their types are equivalent
    and private datatypeCtorEq (typeArgs: Map<string, string>) (c1: DatatypeCtor) (c2: DatatypeCtor) : bool =
        c1.Name = c2.Name
        && forallSafe
            (fun (x: DatatypeDestructor) (y: DatatypeDestructor) ->
                (typeEq (typeName <| c1.EnclosingDatatype) typeArgs x.Type y.Type))
            (fromList c1.Destructors)
            (fromList c2.Destructors)

    // Newtype equality is similar; we have to check the base types and the conditions for equality
    and private updateNewTypeEq (d1: NewtypeDecl) (d2: NewtypeDecl) : bool =
        // Again, short-circuit if we have already computed the result or can easily tell the answer
        let fstName = typeName d1
        let sndName = typeName d2
        let sameName = fstName = sndName

        let res =
            sameName
            && not (diff.Contains(fstName))
            && (same.Contains(fstName)
                || (typeEq "" Map.empty d1.BaseType d2.BaseType
                    && ((d1.Var = null && d2.Var = null)
                        || exprEq (Some(d1.Var.Name, d2.Var.Name)) d1.Constraint d2.Constraint)))

        let setToAdd = if res then same else diff

        (if sameName then
             ignore (setToAdd.Add(fstName))
             updateDict oldDecls fstName (d1 :> TopLevelDecl)
             updateDict newDecls sndName (d2 :> TopLevelDecl))

        res

    // This handles both pure type synonyms and subset types (we ignore the subset condition for now; handling it
    // is quite complicated). Not all of these types need to be translated, but we need to know which are equal.
    // We defer the decision of what needs to be translated to the type injection generation.
    // This function is quite simple; we just compare the names and the equivalence of the base types.
    and private updateTypeSynonymEq (t1: TypeSynonymDecl) (t2: TypeSynonymDecl) : bool =
        // Similarly to updateDataTypeEq, we first look up the result
        let fstName = typeName t1
        let sndName = typeName t2
        let sameName = fstName = sndName

        let res =
            sameName
            && not (diff.Contains(fstName))
            && (same.Contains(fstName)
                || (typeEq "" (typeArgMap (fromList t1.TypeArgs) (fromList t2.TypeArgs)) t1.Rhs t2.Rhs))

        let setToAdd = if res then same else diff

        (if sameName then
             ignore (setToAdd.Add(fstName))
             updateDict oldDecls fstName (t1 :> TopLevelDecl)
             updateDict newDecls sndName (t2 :> TopLevelDecl))

        res

    and private updateClassTypeEq (c1: ClassDecl) (c2: ClassDecl) : bool =
        let fstName = typeName c1
        let sndName = typeName c2
        let sameName = fstName = sndName

        let c1Fields = fieldsOf c1
        let c2Fields = fieldsOf c2

        let res =
            sameName
            && synCheckClass c1
            && synCheckClass c2
            && not (diff.Contains(fstName))
            && (same.Contains(fstName)
                || (c1Fields.Length = c2Fields.Length
                    && c1.TypeArgs.Count = c2.TypeArgs.Count
                    // TODO: this implementation will equa-fy two classes with no fields, but same name and type parameters
                    && forallSafe
                        (matchMembers (typeArgMap (fromList c1.TypeArgs) (fromList c2.TypeArgs)))
                        (List.sortBy (fun x -> x.Name) c1Fields)
                        (List.sortBy (fun x -> x.Name) c2Fields)))

        let setToAdd = if res then same else diff

        (if sameName then
             ignore (setToAdd.Add(fstName))
             updateDict oldDecls fstName (c1 :> TopLevelDecl)
             updateDict newDecls sndName (c2 :> TopLevelDecl))

        res

    and private matchMembers (typeArgs: Map<string, string>) (f1: Field) (f2: Field) : bool =
        match (f1, f2) with
        // we need to check for ConstantField separately because
        // ConstantField permits the initialising expression, whereas Field does not.
        | :? ConstantField as c1, (:? ConstantField as c2) -> constantFieldEq typeArgs c1 c2
        // TODO: decide about DatatypeDestructor and SpecialField
        // Field includes ConstantField, DatatypeDestructor, SpecialField
        | _, _ -> fieldEq typeArgs f1 f2

    and private constantFieldEq (typeArgs: Map<string, string>) (c1: ConstantField) (c2: ConstantField) : bool =
        fieldEq typeArgs c1 c2
        && ((c1.Rhs = null && c2.Rhs = null)
            || exprEq None c1.Rhs c2.Rhs)

    // Field inherits to ConstantField, DatatypeDestructor, SpecialField
    and private fieldEq (typeArgs: Map<string, string>) (f1: Field) (f2: Field) : bool =
        f1.Name = f2.Name
        && f1.IsStatic = f2.IsStatic
        // TODO: how HasStaticKeyword is different from IsStatic
        && f1.HasStaticKeyword = f2.HasStaticKeyword
        && f1.IsGhost = f2.IsGhost
        && f1.IsMutable = f2.IsMutable
        && f1.IsUserMutable = f2.IsUserMutable
        && f1.IsRefining = f2.IsRefining
        && f1.Type.TypeArgs.Count = f2.Type.TypeArgs.Count
        && typeEq (typeName <| f1.EnclosingClass) typeArgs f1.Type f2.Type

    // Compare two types for equivalence - this is the only function external callers need to know about
    let public compareTypeEq (t1: TopLevelDecl) (t2: TopLevelDecl) : bool =
        match (t1, t2) with
        | :? DatatypeDecl as d1, (:? DatatypeDecl as d2) -> updateDataTypeEq d1 d2
        | :? NewtypeDecl as n1, (:? NewtypeDecl as n2) -> updateNewTypeEq n1 n2
        | :? TypeSynonymDecl as t1, (:? TypeSynonymDecl as t2) -> updateTypeSynonymEq t1 t2
        | :? ClassDecl as c1, (:? ClassDecl as c2) -> updateClassTypeEq c1 c2
        | _, _ -> false
