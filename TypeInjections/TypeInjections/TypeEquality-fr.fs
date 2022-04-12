// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT

namespace TypeInjections

open System.IO
open System.Collections.Generic
open UtilsFR
open YIL

// Before generating injections, we want to determine which types are equal and which are not. This module
// contains that logic.
module TypeEqualityFR =

    // We want to memoize the computation so that we don't need to compute the result multiple times if a type is
    // referenced in other types. Using mutable state is cleaner than passing around sets everywhere
    let same : HashSet<string> = HashSet<string>()
    let diff : HashSet<string> = HashSet<string>()

    // Stores the decls for each type that we know is equal, since we will need to reference these decls later
    let oldDecls : Dictionary<string, Decl> = Dictionary<string, Decl>()
    let newDecls : Dictionary<string, Decl> = Dictionary<string, Decl>()

    // Given two same-length lists of TypeParameters, construct a mapping from one to the other
    // This allows us to deal with types that change the names of generic arguments, as long as the order is preserved
    let rec private typeArgMap (l1: string list) (l2: string list) : Map<string, string> =
        List.fold2 (fun m x y -> Map.add x y m) Map.empty l1 l2

    // Check the equality of the expressions for newtypes. This is a syntactic equivalence check, so two expressions
    // may be logically equivalent but be marked as inequivalent. This supports equalities and inequalities (including
    // compound inequalities) and boolean operators.
    // "names" denotes the names of the two variables (ie: x in type foo = x | p(x)). We take in both names, since
    // we allow the two newtypes to use different variable names, as long as the use is consistent.
    let rec private exprEq (names: (string * string) option) (e1: Expr) (e2: Expr) : bool = true

    // The equality computation consists of several mutually recursive functions. The "update_" functions are the
    // top level functions for each type decl (ie: DatatypeDecl, NewtypeDecl, etc), and they update the above maps as well.

    // The core function that checks for type equivalence, subject to the given typeArgs map between generic parameters.
    // currTypeName is the name of the two types (equality of names is checked before calling this function) and is used
    // for recursive types.
    // NOTE: this results in a stack overflow on mutually recursive types. It is difficult to fix this without degrading
    // performance
    let rec private typeEq (currTypeName: string) (typeArgs: Map<string, string>) (t1: Type) (t2: Type) : bool = true

    and private updateDataTypeEq
        (name1: string, tpvars1: string list, ctrs1: DatatypeConstructor list, mem1: Decl list, meta1: Meta)
        (name2: string, tpvars2: string list, ctrs2: DatatypeConstructor list, mem2: Decl list, meta2: Meta)
        : bool =
        // We short circuit if we can easily tell that the types are equal or not.
        // This occurs if the names are different or if we find the names in one of the two known sets.
        let sameName = name1 = name2

        let res =
            sameName
            && not (diff.Contains(name1))
            && (same.Contains(name2)
                || (tpvars1.Length = tpvars2.Length
                    &&
                    // sort constructor lists - the constructors are allowed to be reordered
                    forallSafe
                        (datatypeCtorEq (typeArgMap tpvars1 tpvars2) name1)
                        (List.sortBy (fun x -> x.name) ctrs1)
                        (List.sortBy (fun x -> x.name) ctrs2)))

        let setToAdd = if res then same else diff
        // Only update maps for types with the same name (otherwise, we may introduce false negatives - for instance,
        // we may have List<Foo> and List<Bar>, but Foo and Bar should not necessarily be marked as inequivalent to
        // their corresponding decls)
        (if sameName then
             ignore (setToAdd.Add(name1))
             updateDict oldDecls name1 (Datatype((name1, tpvars1, ctrs1, mem1, meta1)))
             updateDict newDecls name2 (Datatype((name2, tpvars2, ctrs2, mem2, meta2))))

        res

    // Two datatype constructors are equivalent if they have the same name and all of their types are equivalent
    and private datatypeCtorEq
        (typeArgs: Map<string, string>)
        (typeName: string)
        (c1: DatatypeConstructor)
        (c2: DatatypeConstructor)
        : bool =
        c1.name = c2.name
        && forallSafe (fun (x: LocalDecl) (y: LocalDecl) -> (typeEq typeName typeArgs x.tp y.tp)) c1.ins c2.ins

    and private updateTypeDefEq
        (name1: string, tpvars1: string list, super1: Type, pred1: (string * Expr) option, isNew1: bool, meta1: Meta)
        (name2: string, tpvars2: string list, super2: Type, pred2: (string * Expr) option, isNew2: bool, meta2: Meta)
        : bool =

        // Similarly to updateDataTypeEq, we first look up the result
        let sameName = name1 = name2

        // This handles both pure type synonyms and subset types (we ignore the subset condition for now; handling it
        // is quite complicated). Not all of these types need to be translated, but we need to know which are equal.
        // We defer the decision of what needs to be translated to the type injection generation.
        // This function is quite simple; we just compare the names and the equivalence of the base types.
        let updateTypeSynNewTypeNoPredEq
            (isNew: bool)
            (name1: string, tpvars1: string list, super1: Type, meta1: Meta)
            (name2: string, tpvars2: string list, super2: Type, meta2: Meta)
            : bool =
            // new types are not parametrized
            let typParamMap =
                if isNew then
                    Map.empty
                else
                    (typeArgMap tpvars1 tpvars2)

            let res =
                sameName
                && not (diff.Contains(name1))
                && (same.Contains(name1)
                    || (typeEq "" typParamMap super1 super2))

            let setToAdd = if res then same else diff

            (if sameName then
                 ignore (setToAdd.Add(name1))
                 updateDict oldDecls name1 (TypeDef(name1, tpvars1, super1, None, isNew, meta1))
                 updateDict newDecls name2 (TypeDef(name2, tpvars2, super2, None, isNew, meta2)))

            res

        // Newtype equality is similar; we have to check the base types and the conditions for equality
        let updateNewSubTypeWithConstraintEq
            (isNew: bool)
            (name1: string, tpvars1: string list, super1: Type, var1: string, cExp1: Expr, meta1: Meta)
            (name2: string, tpvars2: string list, super2: Type, var2: string, cExp2: Expr, meta2: Meta)
            : bool =

            // new types are not parametrized
            let typParamMap =
                if isNew then
                    Map.empty
                else
                    (typeArgMap tpvars1 tpvars2)

            let res =
                sameName
                && not (diff.Contains(name1))
                && (same.Contains(name1)
                    || (typeEq "" typParamMap super1 super2
                        && ((var1 = "" && var2 = "")
                            || exprEq (Some(var1, var2)) cExp1 cExp2)))

            let setToAdd = if res then same else diff

            (if sameName then
                 ignore (setToAdd.Add(name1))
                 updateDict oldDecls name1 (TypeDef(name1, tpvars1, super1, Some(var1, cExp1), true, meta1))
                 updateDict newDecls name1 (TypeDef(name2, tpvars2, super2, Some(var2, cExp2), true, meta2)))

            res

        match (isNew1, isNew2, pred1, pred2) with
        // type Synonyms
        | false, false, None, None ->
            updateTypeSynNewTypeNoPredEq false (name1, tpvars1, super1, meta1) (name2, tpvars2, super2, meta2)
        // subset types
        | false, false, Some (var1, cExp1), Some (var2, cExp2) ->
            updateNewSubTypeWithConstraintEq
                false
                (name1, tpvars1, super1, var1, cExp1, meta1)
                (name2, tpvars2, super2, var2, cExp2, meta2)
        // new types
        // newtype foo = real (permitted), predicates could be None or Some
        // newtype with no predicate
        | true, true, None, None ->
            updateTypeSynNewTypeNoPredEq true (name1, tpvars1, super1, meta1) (name2, tpvars1, super2, meta2)
        // newtype with predicate
        | true, true, Some (var1, cExp1), Some (var2, cExp2) ->
            updateNewSubTypeWithConstraintEq
                true
                (name1, tpvars1, super1, var1, cExp1, meta1)
                (name2, tpvars2, super2, var2, cExp2, meta2)
        | _, _, _, _ -> true


    // Compare two types for equivalence - this is the only function external callers need to know about
    let public compareTypeEq (t1: Decl) (t2: Decl) : bool =
        match (t1, t2) with
        | Datatype (name1, tpvs1, constructors1, members1, meta1),
          Datatype (name2, tpvs2, constructors2, members2, meta2) ->
            updateDataTypeEq
                (name1, tpvs1, constructors1, members1, meta1)
                (name2, tpvs2, constructors2, members2, meta2)
        | TypeDef (name1, tpvs1, super1, pred1, isNew1, meta1), TypeDef (name2, tpvs2, super2, pred2, isNew2, meta2) ->
            updateTypeDefEq (name1, tpvs1, super1, pred1, isNew1, meta1) (name2, tpvs2, super2, pred2, isNew2, meta2)
        | _, _ -> false
