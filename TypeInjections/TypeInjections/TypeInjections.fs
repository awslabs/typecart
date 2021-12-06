// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT

namespace TypeInjections

open System.Collections.Generic
open Microsoft.Boogie
open Microsoft.Dafny
open Utils
open NameUtils
open TypeEquality

// Handles the logic for generating the type injection functions as AST nodes
module TypeInjections =

    // For a few parts in the translation process (for now, for mapping type translations over sequences, sets, and maps),
    // we want to include extra functions in the output file. It is easiest to read them and store them as AST nodes
    // from an extra input file. The following map and set store the parsed ASTs and determine which we need to include
    // in the output.
    let extraFunctions = Dictionary<string, Function>()
    let extraFunctionsNeeded = HashSet<string>()
    // extra function names (these are builtin; it's not super extensible at the moment)
    let private seqMapName = "seqMap"
    let private setMapName = "setMap"
    let private mapKeyName = "mapMapKey"
    let private mapValName = "mapMapValue"
    let private mapMapName = "mapMap"

    // list of function names for typeArgs
    let private typeArgsFName (t: List<TypeParameter>) : string list =
        let typeArgFName (d: TypeParameter) : string = "f" + d.Name

        List.map typeArgFName (fromList t)

    let private typeParams (ts: List<Type>) : List<TypeParameter> =
        let ts = ts |> fromList

        (List.choose
            (fun (t: Type) ->
                match t with
                | :? UserDefinedType as u ->
                    match u.ResolvedClass with
                    | :? TypeParameter as p -> Some p
                    | _ -> None
                | _ -> None)
            ts)
        |> List<TypeParameter>

    let rec private actualBindings (names: string list) : ActualBinding list =
        match names with
        | [] -> []
        | n :: ns ->
            ActualBinding(null, genNameSegment n)
            :: actualBindings ns

    // For subset types (ex: seq32<Object>), we want to get the base type with the given parameters (ex: seq<Object>)
    // This is limited, and only allows built-in collection types to have type arguments
    let private subsetRhs (u: UserDefinedType) : Type =
        match u.ResolvedClass with
        | :? SubsetTypeDecl as s ->
            match s.Rhs with
            | :? SetType as st -> SetType(st.Finite, u.TypeArgs.[0]) :> Type
            | :? SeqType -> SeqType(u.TypeArgs.[0]) :> Type
            | :? MapType as m -> MapType(m.Finite, u.TypeArgs.[0], u.TypeArgs.[1]) :> Type
            | _ -> s.Rhs
        | _ ->
            System.Console.WriteLine("Can only be used for subset types")
            null

    // In several places, we handle builtin types differently, since they don't need as much manual translation.
    // The function denotes whether the input type is builtin (None) or not (Some).
    // If a type is not builtin, then there is a user-defined type somewhere that we need to translate. This function
    // also gives us the NameSegment corresponding to the translation function for this type,
    // or either/both for the case of maps (where we might need to translate both the key and value types).
    // All cases other than maps are handled by Left(NameSegment).
    // Maps result in Right(n1, n2), options denoting the domain and range NameSegment options, respectively.
    // There cannot be any other user-defined NameSegments, since we do not support such types yet (such as List<Object>).
    let rec private isTypeBuiltin
        (x: Type)
        : Either<ActualBinding, ActualBinding Option * ActualBinding Option> Option =
        match x with
        | :? UserDefinedType as u ->
            match u.ResolvedClass with
            | :? SubsetTypeDecl -> isTypeBuiltin (subsetRhs u)
            | :? NewtypeDecl as n -> Some(Left(genbinding (typeTranslationName n)))
            | :? TypeSynonymDecl as t -> isTypeBuiltin t.Rhs
            | :? DatatypeDecl as d -> Some(Left(genbinding (typeTranslationName d)))
            | :? ClassDecl as c -> Some(Left(genbinding (typeTranslationName c)))
            | :? TypeParameter as typeArg -> Some(Left(genbinding ("f" + typeArg.Name)))
            | _ -> None
        | :? IntType
        | :? BoolType
        | :? CharType
        | :? RealType
        | :? BitvectorType -> None
        // We do not currently allow nested set, seq, etc with non-builtin types
        | :? SeqType as s -> isTypeBuiltin s.Arg
        | :? SetType as s -> isTypeBuiltin s.Arg
        | :? MapType as m ->
            // For maps, we just need to mark which of the types is the domain and which is the range
            match (isTypeBuiltin m.Domain), (isTypeBuiltin m.Range) with
            | None, None -> None
            | Some (Left n), None -> Some(Right(Some n, None))
            | None, Some (Left n) -> Some(Right(None, Some n))
            | Some (Left n1), Some (Left n2) -> Some(Right(Some n1, Some n2))
            | _, _ -> None // do not allow nested maps
        | _ -> None

    // Generate the list of Bound Variables from a datatype constructor's arguments (ex: for Foo(x: int, y:seq<Bar>),
    // we need to generate the BoundVars for x and y)
    // This is almost very simple, but Dafny's pretty printer does not print the full qualified name for a type, so
    // we need to construct some new types with the full names (or else the generated name is ambigious).
    let private genBoundVars (c: DatatypeCtor) : List<BoundVar> =
        // The Dafny pretty printer does not print the full qualified name for the type. (for example, Old.Foo just
        // prints as Foo, which is ambigious). To ensure that the result is valid Dafny, we need to create a new type
        // with the full name
        let rec qualifiedType (t: Type) : Type =
            match t with
            | :? UserDefinedType as u ->
                match u.ResolvedClass with
                | :? DatatypeDecl
                | :? NewtypeDecl ->
                    UserDefinedType(
                        Token.NoToken,
                        getModulePath u,
                        u.ResolvedClass,
                        List<Type>(List.map qualifiedType (fromList t.TypeArgs))
                    )
                    :> Type
                | :? TypeSynonymDecl ->
                    if u.FullName.StartsWith("_") // default/system types - we can just use their name (for string, which is a builtin type synonym)
                    then
                        t
                    else
                        UserDefinedType(
                            Token.NoToken,
                            getModulePath u,
                            u.ResolvedClass,
                            List<Type>(List.map qualifiedType (fromList t.TypeArgs))
                        )
                        :> Type

                | _ -> t
            | :? SeqType as s -> SeqType(qualifiedType s.Arg) :> Type
            | :? SetType as s -> SetType(s.Finite, qualifiedType s.Arg) :> Type
            | :? MapType as m -> MapType(m.Finite, qualifiedType m.Domain, qualifiedType m.Range) :> Type
            | _ -> t

        List<BoundVar>(
            List.map
                (fun (x: DatatypeDestructor) -> BoundVar(Token.NoToken, x.Name, qualifiedType x.Type))
                (fromList c.Destructors)
        )

    // Get the Expression corresponding to the given datatype constructor, including all nested module names
    // For example, gets constructor name Old.A.B.foo as a nested Expression
    let private ctorModuleExpr (c: DatatypeCtor) : Expression =
        let modules = c.FullName.Substring(1).Split(".") //name starts with #; remove this

        let rec genExpr (l: string list) : Expression =
            match l with
            | [] -> null
            | [ name ] -> NameSegment(Token.NoToken, name, List<Type>()) :> Expression
            | name :: tl -> ExprDotName(Token.NoToken, genExpr tl, name, List<Type>()) :> Expression

        genExpr (List.rev <| (fromList <| List<string>(modules)))

    let private genActualBindings (tArgs: List<Type>) : ActualBinding list =
        let tArgs = tArgs |> fromList

        let genLambda (t: Type) : Expression Option =
            match isTypeBuiltin t with
            | None ->
                Some(
                    LambdaExpr(
                        Token.NoToken,
                        singleList (BoundVar(Token.NoToken, "x", t)),
                        null,
                        List<FrameExpression>(),
                        genNameSegment "x"
                    )
                    :> Expression
                )
            | Some (Left _) ->
                match t with
                | :? UserDefinedType as u ->
                    match u.ResolvedClass with
                    | :? TypeParameter as t ->
                        let typeArgFName (t: TypeParameter) : string = "f" + t.Name
                        Some((genNameSegment (typeArgFName t)) :> Expression)
                    | _ -> None
                | _ -> None
            | _ -> None

        let genLambdas = List.choose genLambda tArgs

        List.map (fun e -> ActualBinding(null, e)) genLambdas

    // This is a crucial function that generates the expression to apply the needed type transformation function to an argument.
    // For builtin types, we can just return a NameSegment of the argument name, since we don't need to translate anything.
    // For datatypes and newtypes that require translation, we need to use an ApplySuffix to apply the necessary translation
    // function to the argument.
    // The complicated part comes from collection types, where we need to use the appropriate mapping function to translate
    // (for example: x: set<Foo> requires setMap(FooOldToNew, x)). For maps, we want to select the appropriate mapping
    // based on whether the keys, values, or both need to be translated
    // NOTE: we do not allow nested non-builtin collection types (ie seq<seq<Foo>>)
    let rec private genArgExpr (x: Type) (name: string) : Expression =
        // All collection types are similar; we need to map the type translation function over the collection. We
        // can abstract this out for all cases except maps where we need to translate both keys and values; it's a bit different.
        let genArgExprColl (mapFunctionName: string) (translateName: ActualBinding) : Expression =
            if not (extraFunctionsNeeded.Contains(mapFunctionName)) then
                ignore (extraFunctionsNeeded.Add(mapFunctionName))

            let bindings =
                List<ActualBinding>(
                    [ translateName
                      ActualBinding(null, genNameSegment name) ]
                )

            ApplySuffix(Token.NoToken, null, genNameSegment mapFunctionName, bindings) :> Expression

        match isTypeBuiltin x with
        | None -> genNameSegment name :> Expression // we can just copy the argument directly
        | Some (Left n) ->
            match x with
            | :? UserDefinedType as u ->
                match u.ResolvedClass with
                | :? SubsetTypeDecl -> genArgExpr (subsetRhs u) name
                | :? TypeSynonymDecl as t -> genArgExpr t.Rhs name
                | :? DatatypeDecl ->

                    let bindings =
                        genActualBindings x.TypeArgs
                        @ [ ActualBinding(null, genNameSegment name) ]
                        |> List<ActualBinding>

                    ApplySuffix(Token.NoToken, null, n.Actual, bindings) :> Expression
                // TODO: need to test, might not work for parametric types
                | :? ClassDecl ->

                    let bindings =
                        genActualBindings x.TypeArgs
                        @ [ ActualBinding(null, genNameSegment name) ]
                        |> List<ActualBinding>

                    ApplySuffix(Token.NoToken, null, n.Actual, bindings) :> Expression
                | :? NewtypeDecl ->
                    ApplySuffix(Token.NoToken, null, n.Actual, singleList (ActualBinding(null, genNameSegment name)))
                    :> Expression
                | :? TypeParameter ->
                    ApplySuffix(Token.NoToken, null, n.Actual, singleList (ActualBinding(null, genNameSegment name)))
                    :> Expression
                | _ -> null
            | :? SeqType -> // we know that we will need to map, or else we would have gotten None above
                genArgExprColl seqMapName n
            | :? SetType -> // similar to seqType
                genArgExprColl setMapName n
            | _ -> null
        // in all of these cases, we know that the type is map<K, V>
        | Some (Right (Some n, None)) -> // only key needs to be translated
            genArgExprColl mapKeyName n
        | Some (Right (None, Some n)) -> // only value needs to be translated
            genArgExprColl mapValName n
        | Some (Right (Some k, Some v)) -> // both key and value need to be translated
            if not (extraFunctionsNeeded.Contains(mapMapName)) then
                ignore (extraFunctionsNeeded.Add(mapMapName))

            let bindings =
                List<ActualBinding>(
                    [ k
                      v
                      ActualBinding(null, genNameSegment name) ]
                )

            ApplySuffix(Token.NoToken, null, genNameSegment mapMapName, bindings) :> Expression
        | _ -> null

    // Expression for giving arguments to a datataype constructor - ex: Old.A.B.foo(x, y), where B = foo(x : int, y : Object)
    let private applyCtorToArgsExpr (l: List<BoundVar>) (c: DatatypeCtor) : Expression =
        let bindings =
            List<ActualBinding>(
                List.map (fun (x: BoundVar) -> ActualBinding(null, genArgExpr x.Type x.Name)) (fromList l)
            )

        ApplySuffix(Token.NoToken, null, ctorModuleExpr c, bindings) :> Expression

    // Generate the case corresponding to the translation from the (old) constructor c1 to the (new) constructor c2
    let private genDatatypeCtorExpr (c1: DatatypeCtor) (c2: DatatypeCtor) : MatchCaseExpr =
        if c1.Destructors.Count = 0 then
            MatchCaseExpr(Token.NoToken, c1, List<BoundVar>(), ctorModuleExpr c2)
        else
            let boundVars = genBoundVars c1
            MatchCaseExpr(Token.NoToken, c1, boundVars, applyCtorToArgsExpr boundVars c2)

    // Generate the body of a translation function for a datatype, where the name of the input to the function is argName
    let private genDatatypeFunBody (d1: DatatypeDecl) (d2: DatatypeDecl) (argName: string) : Expression =
        let sortedCtors1 =
            List.sortBy (fun (x: DatatypeCtor) -> x.Name) (fromList d1.Ctors)

        let sortedCtors2 =
            List.sortBy (fun (x: DatatypeCtor) -> x.Name) (fromList d2.Ctors)

        MatchExpr(
            Token.NoToken,
            NameSegment(Token.NoToken, argName, null),
            List<MatchCaseExpr>(List.map2 genDatatypeCtorExpr sortedCtors1 sortedCtors2),
            false,
            null
        )
        :> Expression

    // Get the generic type arguments for the function declaration
    let private listOfTypeParams (x: List<TypeParameter>) : List<Type> =
        List<Type>(List.map (fun (x: TypeParameter) -> UserDefinedType x :> Type) (fromList x))

    // new type parameters for the return type, we replace only the names of type parameters of the
    // type we are trying to map into, keeping other fields of `TypeParameter` intact
    let private typeArgsOut (t1: List<TypeParameter>) (t2: List<TypeParameter>) : List<TypeParameter> =
        let replaceName (name: string) (t: TypeParameter) : TypeParameter =
            TypeParameter(t.tok, name, t.VarianceSyntax)

        // new unique name
        let typeArgName (d: TypeParameter) : string = d.Name + "'"

        // list of names of d1.TypeArgs
        let typeArgsName (t: List<TypeParameter>) : string list = List.map typeArgName (fromList t)

        // non-conflicting names for d2.TypeArgs
        let typeArgs (t1: List<TypeParameter>) (t2: List<TypeParameter>) : List<TypeParameter> =
            List.map2 replaceName (typeArgsName t1) (fromList t2)
            |> List<TypeParameter>

        if t1.Count <> t2.Count then
            failwith "type parameters of identically defined types must have same size"

        typeArgs t1 t2

    // type of mapping function for typeArgs, will always have arity 2
    let private typeArgsConv (t1: List<TypeParameter>) (t2: List<TypeParameter>) : Formal list =

        let argArrowType (arg: TypeParameter) (result: TypeParameter) =
            let args : List<Type> =
                let args = List<Type>()
                args.Add(UserDefinedType arg :> Type)
                args.Add(UserDefinedType result :> Type)
                args

            UserDefinedType(Token.NoToken, ArrowType.TotalArrowTypeName(2), args)

        let typeArgs =
            List.map2 argArrowType (fromList t1) (fromList t2)

        let mkFormal name fType =
            Formal(Token.NoToken, name, fType, true, false, null, false)

        let funcTypeArgs = typeArgsFName t1

        List.map2 mkFormal funcTypeArgs typeArgs

    //// Full function generation:
    // Generate the translation function between two datatypes
    let private genDatatypeInj (d1: DatatypeDecl) (d2: DatatypeDecl) : MemberDecl =
        let funcName = typeTranslationName d1
        // We use the first letter of the type name as the function input (ex: the input to FooOldToNew is called f)
        let argName = d1.Name.Substring(0, 1).ToLower()

        let inputType =
            UserDefinedType(Token.NoToken, d1.FullName, d1, listOfTypeParams d1.TypeArgs)

        let d2TypeArgs = typeArgsOut d1.TypeArgs d2.TypeArgs

        let funcArg =
            Formal(Token.NoToken, argName, inputType, true, false, null, false)

        let funcTypeArgs = typeArgsConv d1.TypeArgs d2TypeArgs

        let funcArgs =
            List.append funcTypeArgs [ funcArg ]
            |> List<Formal>

        let outputType =
            UserDefinedType(Token.NoToken, d2.FullName, d2, listOfTypeParams d2TypeArgs)

        //decreases clause
        let exprs =
            singleList (AutoGeneratedExpression(Token.NoToken, IdentifierExpr(Token.NoToken, argName)) :> Expression)

        // generate body of function
        let body = genDatatypeFunBody d1 d2 argName

        Function(
            Token.NoToken,
            funcName,
            false,
            false,
            concatList d1.TypeArgs d2TypeArgs,
            funcArgs,
            null,
            outputType,
            List<AttributedExpression>(),
            List<FrameExpression>(),
            List<AttributedExpression>(),
            Specification<Expression>(exprs, null),
            body,
            Token.NoToken,
            null,
            null,
            null
        )
        :> MemberDecl

    // Generate injection function for newtype
    let private genNewtypeInj (d1: NewtypeDecl) (d2: NewtypeDecl) : MemberDecl =
        // Very similar to datatype except that the function body is much simpler and we don't need to worry about typeArgs
        let funcName = typeTranslationName d1
        let argName = d1.Name.Substring(0, 1).ToLower()
        // return argument name is ' version of the input argument
        // return name is required for ensure clause
        let retName = d1.Name.Substring(0, 1).ToLower() + "'"

        let inputType =
            UserDefinedType(Token.NoToken, d1.FullName, d1, List<Type>())

        let outputType =
            UserDefinedType(Token.NoToken, d2.FullName, d2, List<Type>())

        let baseType = d1.BaseType

        let funcArgs =
            singleList (Formal(Token.NoToken, argName, inputType, true, false, null, false))

        let retArg =
            Formal(Token.NoToken, retName, outputType, false, false, null, false)
        //decreases clause
        let decExpr =
            singleList (AutoGeneratedExpression(Token.NoToken, IdentifierExpr(Token.NoToken, argName)) :> Expression)

        let ensureExpr =
            singleList (
                AttributedExpression(
                    BinaryExpr(
                        Token.NoToken,
                        BinaryExpr.Opcode.Eq,
                        ConversionExpr(Token.NoToken, IdentifierExpr(Token.NoToken, argName), baseType),
                        ConversionExpr(Token.NoToken, IdentifierExpr(Token.NoToken, retName), baseType)
                    )
                )
            )

        // function body
        let body =
            ConversionExpr(
                Token.NoToken,
                ParensExpression(Token.NoToken, ConversionExpr(Token.NoToken, genNameSegment argName, d1.BaseType)),
                outputType
            )

        Function(
            Token.NoToken,
            funcName,
            false,
            false,
            List<TypeParameter>(),
            funcArgs,
            retArg,
            outputType,
            List<AttributedExpression>(),
            List<FrameExpression>(),
            List<AttributedExpression> ensureExpr,
            Specification<Expression>(decExpr, null),
            body,
            Token.NoToken,
            null,
            null,
            null
        )
        :> MemberDecl

    // For type synonyms and subset types that are nontrivial (ie, have user-defined datatypes or newtypes somewhere),
    // we need to generate functions.
    let private genTypeSynonymInj (d1: TypeSynonymDecl) (d2: TypeSynonymDecl) : MemberDecl =
        // Similar to datatype
        let funcName = typeTranslationName d1
        let argName = d1.Name.Substring(0, 1).ToLower()

        let inputType =
            UserDefinedType(Token.NoToken, d1.FullName, d1, listOfTypeParams d1.TypeArgs)

        let d2TypeArgs = typeArgsOut d1.TypeArgs d2.TypeArgs

        let funcArg =
            Formal(Token.NoToken, argName, inputType, true, false, null, false)

        let funcTypeArgs = typeArgsConv d1.TypeArgs d2TypeArgs
        // add the type input parameter to the end, for consistency reasons
        let funcArgs =
            List.append funcTypeArgs [ funcArg ]
            |> List<Formal>

        let outputType =
            UserDefinedType(Token.NoToken, d2.FullName, d2, listOfTypeParams d2TypeArgs)

        //decreases clause
        let exprs =
            singleList (AutoGeneratedExpression(Token.NoToken, IdentifierExpr(Token.NoToken, argName)) :> Expression)

        // generate body of function - this is easy, since we just need a single call to genArgExpr
        let body = genArgExpr d1.Rhs argName

        let constraintExp (t: TypeSynonymDecl) : (BoundVar * Expression) option =
            match t with
            | :? SubsetTypeDecl as s -> Some(s.Var, s.Constraint)
            | _ -> None

        // replace bound variable of the subset declaration with the given expression
        let genReqExp var exp expReplace =
            let substMap =
                let m = Dictionary<IVariable, Expression>()
                m.Add(var, expReplace)
                m

            let typeMap = Dictionary<TypeParameter, Type>()

            Substituter(null, substMap, typeMap)
                .Substitute(exp)

        let requireExpr =
            Option.bind
                (fun (var, consExp) ->
                    Some(singleList (AttributedExpression(prefixFullDafnyNames (genReqExp var consExp body)))))
                (constraintExp d2)
            |> Option.defaultValue (List<AttributedExpression>())

        Function(
            Token.NoToken,
            funcName,
            false,
            true,
            concatList d1.TypeArgs d2TypeArgs,
            funcArgs,
            null,
            outputType,
            requireExpr,
            List<FrameExpression>(),
            List<AttributedExpression>(),
            Specification<Expression>(exprs, null),
            body,
            Token.NoToken,
            null,
            null,
            null
        )
        :> MemberDecl

    let private genClassInjFun (c1: ClassDecl) (c2: ClassDecl) : MemberDecl list =
        let funcName = typeTranslationName c1
        let methodName = funcName + "Method"

        // We use the first letter of the type name as the function input (ex: the input to FooOldToNew is called f)
        let argName = c1.Name.Substring(0, 1).ToLower()
        // return argument name is ' version of the input argument
        // return name is required for ensure clause
        let retName = c1.Name.Substring(0, 1).ToLower() + "'"

        let inputType =
            UserDefinedType(Token.NoToken, c1.FullName, c1, listOfTypeParams c1.TypeArgs)

        let c2TypeArgs = typeArgsOut c1.TypeArgs c2.TypeArgs

        let outputType =
            UserDefinedType(Token.NoToken, c2.FullName, c2, listOfTypeParams c2TypeArgs)

        let funcArg =
            Formal(Token.NoToken, argName, inputType, true, false, null, false)

        let funcTypeArgs = typeArgsConv c1.TypeArgs c2TypeArgs

        let retArg =
            Formal(Token.NoToken, retName, outputType, false, false, null, false)

        let funcArgs =
            List.append funcTypeArgs [ funcArg ]
            |> List<Formal>

        let outputType =
            UserDefinedType(Token.NoToken, c2.FullName, c2, listOfTypeParams c2TypeArgs)

        //decreases clause
        let exprs =
            singleList (AutoGeneratedExpression(Token.NoToken, IdentifierExpr(Token.NoToken, argName)) :> Expression)

        let c1Fields =
            List.sortBy (fun (x: Field) -> x.Name) (fieldsOf c1)

        let c2Fields =
            List.sortBy (fun (x: Field) -> x.Name) (fieldsOf c2)

        let c2FieldNames =
            List.map (fun (f: Field) -> f.Name) c2Fields

        let lhsExps =
            List.map (fun (name: string) -> MemberSelectExpr(Token.NoToken, genNameSegment retName, name)) c2FieldNames

        let funRhsExp =
            let c1FieldNames =
                List.map (fun (f: Field) -> argName + "." + f.Name) c1Fields

            let c1FieldTypes =
                List.map (fun (f: Field) -> f.Type) c1Fields

            List.map2 (fun (t: Type) (name: string) -> genArgExpr t name) c1FieldTypes c1FieldNames

        let funEnsureExprs =
            List.map2
                (fun e1 e2 -> AttributedExpression(BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Eq, e1, e2)))
                lhsExps
                funRhsExp
            |> List<AttributedExpression>

        let methodEnsureExprs =

            let rhsExp = genArgExpr inputType argName

            let rhsExps =
                List.map (fun (name: string) -> MemberSelectExpr(Token.NoToken, rhsExp, name)) c2FieldNames

            List.map2
                (fun e1 e2 -> AttributedExpression(BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Eq, e1, e2)))
                lhsExps
                rhsExps
            |> List<AttributedExpression>

        let injFun =
            Function(
                Token.NoToken,
                funcName,
                false,
                false,
                concatList c1.TypeArgs c2TypeArgs,
                funcArgs,
                retArg,
                outputType,
                List<AttributedExpression>(),
                List<FrameExpression>(),
                funEnsureExprs,
                Specification<Expression>(exprs, null),
                null,
                Token.NoToken,
                null,
                null,
                null
            )
            :> MemberDecl

        let genClassMethodBody : BlockStmt =
            let varTemp =
                singleList (LocalVariable(Token.NoToken, Token.NoToken, "temp", outputType, false))

            let varSt =
                let lhsExp =
                    singleList (IdentifierExpr(Token.NoToken, "tmp") :> Expression)

                let constructorArgs =
                    List.map (fun e -> ActualBinding(null, e, false)) funRhsExp
                    |> List<ActualBinding>

                let rhss =
                    singleList (TypeRhs(Token.NoToken, outputType, constructorArgs) :> AssignmentRhs)

                let updSt =
                    UpdateStmt(null, null, lhsExp, rhss, true)

                VarDeclStmt(Token.NoToken, Token.NoToken, varTemp, updSt) :> Statement

            let retSt =
                let rtVar =
                    singleList (ExprRhs(IdentifierExpr(Token.NoToken, "temp"), null) :> AssignmentRhs)

                ReturnStmt(Token.NoToken, Token.NoToken, rtVar) :> Statement

            let methodStmts = [ varSt; retSt ] |> List<Statement>

            BlockStmt(Token.NoToken, Token.NoToken, methodStmts)

        let injMethod =
            Method(
                Token.NoToken,
                methodName,
                false,
                false,
                concatList c1.TypeArgs c2TypeArgs,
                funcArgs,
                singleList retArg,
                List<AttributedExpression>(),
                Specification<FrameExpression>(List<FrameExpression>(), null),
                methodEnsureExprs,
                Specification<Expression>(exprs, null),
                genClassMethodBody,
                null,
                null,
                false
            )
            :> MemberDecl

        [ injFun; injMethod ]


    // Generate the injection function for type name s
    let private genInj (s: string) : MemberDecl list Option =
        let oldDecl = oldDecls.[s]
        let newDecl = newDecls.[s]

        match (oldDecl, newDecl) with
        | :? DatatypeDecl as d1, (:? DatatypeDecl as d2) -> Some([ genDatatypeInj d1 d2 ])
        | :? NewtypeDecl as n1, (:? NewtypeDecl as n2) -> Some([ genNewtypeInj n1 n2 ])
        | :? TypeSynonymDecl as t1, (:? TypeSynonymDecl as t2) ->
            // Although Dafny can prove equivalence automatically for identical built-in type synonyms;
            // we need explicit type casting sometimes while proving theorems,
            // therefore we generate casting functions for built-in types as well
            Some([ genTypeSynonymInj t1 t2 ])
        | :? ClassDecl as c1, (:? ClassDecl as c2) -> Some(genClassInjFun c1 c2)
        | _, _ ->
            System.Console.WriteLine("Only classes, datatypes, newtypes, type synonyms, and subset types supported")
            None

    // Generate the top level module that contains all of the injection functions along with the Old and New imports.
    // This is the only function that is called externally
    let genOuter includeLemmas : ModuleDecl =

        let members = List<MemberDecl>()
        // top level module definition - name "Combine" is hard coded in right now
        let generatedMod =
            ModuleDefinition(
                Token.NoToken,
                "Combine",
                List<IToken>(),
                false,
                false,
                null,
                DefaultModuleDecl(),
                null,
                false,
                true,
                true
            )

        // Generate the old and new import declarations
        let genImportDecl (modName: string) (isOpened: bool) : AliasModuleDecl =
            let token = Token()
            token.``val`` <- modName
            let tokenList = singleList (token :> IToken)
            let id = ModuleQualifiedId(tokenList)
            AliasModuleDecl(id, token, generatedMod, isOpened, List<IToken>())

        // Add injection functions for equivalent types
        List.iter
            (fun (s: string) ->
                match genInj s with
                | None -> ()
                | Some funDefs -> List.iter members.Add funDefs)
            (fromList (List<string>(same)))

        // Add extra functions and injective predicate at beginning of list
        members.Reverse()

        if extraFunctionsNeeded.Contains("setMap") then
            members.Add(extraFunctions.["Injective"])

        List.iter (fun x -> members.Add(extraFunctions.[x])) (fromList (List<string>(extraFunctionsNeeded)))
        members.Reverse()

        let defClass = DefaultClassDecl(generatedMod, members)

        // add imports and all functions to module
        generatedMod.TopLevelDecls.Add(genImportDecl "Old" false)
        generatedMod.TopLevelDecls.Add(genImportDecl "New" false)

        if includeLemmas then
            generatedMod.TopLevelDecls.Add(genImportDecl "Lemmas" true)

        generatedMod.TopLevelDecls.Add(defClass)

        LiteralModuleDecl(generatedMod, DefaultModuleDecl()) :> ModuleDecl
