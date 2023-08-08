namespace TypeInjections

// DotNet
open System
open System.Numerics
open Microsoft.BaseTypes
// Dafny
open Microsoft.Dafny
// Yucca
open Utils

(* convert C# Dafny AST to F# Dafny AST

   adapted from 15bd2b1d9a45fb1799afacd60439454e56f431cd of YuccaDafnyCompiler

   This module contains mutually recursive functions, roughly one for every non-terminal in the syntax of our Dafny fragment.
   The name of each function corresponds to the return type in the F# AST, e.g., program, decl, expr, tp.
   Together, they traverse the C# AST and create corresponding elements in the F# AST.
   We avoid non-trivial transformations in this code and focus on mirroring the C# AST.
   It has the following purposes:
   - It abstracts from the Dafny internals and their C# implementation.
   - It drops C# boilerplate and those parts of the Dafny implementation that are not essential for our purposes.
   - This file is the only one that needs to be reviewed by a Dafny expert or re-reviewed when Dafny changes.
*)
module DafnyToYIL =
    // references to C# input classes are unqualified, all references to output F# types (sometimes of the same name) are qualified with "Y."
    module Y = YIL

    // ***** helper functions
    let warning (msg: string) = Console.WriteLine("WARNING: " + msg)
    let unsupported msg = failwith msg
    let error msg = failwith msg

    // infix operators for recursing into lists (C# list input yields F# list output)
    let (@) f l = List.map f (fromIList l)
    let (@/) f l = List.collect f (fromIList l)

    // special strings that Dafny uses for built-in objects
    let DafnySystem = "_System"
    let DafnyTuple = "_tuple#"
    let DafnyTupleMake = "_#Make" // tuple constructor is named _#Maken for arity n
    let DafnyFun = "_#Func"
    let DafnyTotalFun = "_#TotalFunc"
    let DafnyPartialFun = "_#PartialFunc"
    let DafnyMap = "map"
    let DafnyKeys = "Keys"
    let DafnyValues = "Values"
    let DafnyReads = "reads" // the special 'reads' member of a function
    let DafnyArrayPrefix = "array"
    let DafnyReveal = "reveal_"
    
    let mutable dafnyOptions = DafnyOptions.Default

    // ***** the mutually recursive functions

    (* a program concatenates the input file with all its dependencies, in reverse dependency order
       declarations in a file or module are wrapped in default classes (and a default module if needed)
       and implicitly static *)
    let rec program (p: Program, options: DafnyOptions) : Y.Program =
        let decls = p.DefaultModuleDef.TopLevelDecls
        let declsRev = List.rev (fromIEnumerable decls)
        let ddecls = List.collect decl declsRev
        dafnyOptions <- options

        { name = p.Name
          decls = ddecls
          meta = YIL.emptyMeta }

    // meta information attached to a named declaration
    and namedMeta (dcl: Declaration) : Y.Meta =
        { comment = None
          position = Some(position dcl.tok)
          prelude = ""
          attributes = Map.empty }

    // Dafny does not define a common superclass of INamedRegion and IAttributeBearingDeclaration and F# does not support intersection types
    // So we need to duplicate the method here for Declaration and ModuleDefinition
    and namedMetaModDef (dcl: ModuleDefinition) : Y.Meta =
        { comment = None
          position = Some(position dcl.tok)
          prelude = ""
          attributes = Map.empty }

    // trivial conversion of Dafny source position to YIL source positions
    and position (t: Microsoft.Boogie.IToken) : Y.Position =
        { filename = IO.Path.GetFileName t.filename // whole path would be better, but it'd make error messages system-specific, which breaks the negative tests
          pos = t.pos
          line = t.line
          col = t.col }

    and decl (td: TopLevelDecl) : Y.Decl list =
        match td with
        | :? DatatypeDecl as d ->
            let tpvars = typeParameter @ d.TypeArgs
            let dName = d.Name
            let meta = namedMeta d
            [ Y.Datatype(dName, tpvars, constructorDecl @ d.Ctors, List.concat (memberDecl @ d.Members), meta) ]
        | :? LiteralModuleDecl as d ->
            // TODO check inheritance etc.
            if d.TypeArgs.Count <> 0 then
                unsupported "module with type parameters"

            let ms = fromIEnumerable d.ModuleDef.TopLevelDecls
            let dName = d.Name
            let meta = namedMetaModDef d.ModuleDef
            [ Y.Module(dName, List.collect decl ms, meta) ]
        | :? AliasModuleDecl as d ->
            (* Dafny allows "import M", "import m = M" or "import opened M" where M is a module name.
               Either way, the names of M later appear with fully qualified paths. *)
            // we ignore qualifiers, hoping there won't be a name clash when printing
            // if d.Name <> null then
            //    unsupported "import with qualifier"
            if not (fromIList(d.Exports).IsEmpty) then
                unsupported "import with exports"

            if d.GetCompileName(dafnyOptions) = d.Signature.ModuleDef.DafnyName then
                [ Y.Import(Y.ImportDefault(d.Opened, pathOfModule (d.Signature.ModuleDef))) ]
            else
                [ Y.Import(Y.ImportEquals(d.Opened, d.GetCompileName(dafnyOptions), pathOfModule (d.Signature.ModuleDef))) ]
        | :? TypeSynonymDecl as d ->
            // type synonyms and HOL-style subtype definitions
            let tpvars = typeParameter @ d.TypeArgs

            let super, pred =
                match d with
                | :? SubsetTypeDecl as d ->
                    let bv = boundVar d.Var
                    let witness = match d.WitnessKind with
                                  | SubsetTypeDecl.WKind.CompiledZero -> Y.Witness.CompiledZero
                                  | SubsetTypeDecl.WKind.OptOut -> Y.Witness.OptOut
                                  | _ -> unsupported $"witness kind %s{d.WitnessKind.ToString()}"
                    bv.tp, Some(bv.name, expr d.Constraint, witness)
                | _ -> tp d.Rhs, None

            [ Y.TypeDef(d.Name, tpvars, super, pred, false, namedMeta d) ]
        | :? NewtypeDecl as d ->
            // like SubsetTypeDecl but only for a numeric supertype and new type is not a subtype of the old type
            let predO =
                if d.Var = null then
                    None
                else
                    let bv = boundVar d.Var
                    let witness = match d.WitnessKind with
                                  | SubsetTypeDecl.WKind.CompiledZero -> Y.Witness.CompiledZero
                                  | SubsetTypeDecl.WKind.OptOut -> Y.Witness.OptOut
                                  | _ -> unsupported $"witness kind %s{d.WitnessKind.ToString()}"
                    Some(bv.name, expr d.Constraint, witness)

            [ Y.TypeDef(d.Name, [], tp d.BaseType, predO, true, namedMeta d) ]
        | :? IteratorDecl ->
            unsupported
                "Dafny iterators are too idiosyncratic to be compiled easily to other languages and are therefore not supported"
        | :? DefaultClassDecl as d ->
            // we skip the default class declaration and instead shift its members to the containing module
            List.concat (memberDecl @ d.Members)
        | :? ClassDecl as d ->
            let dName = d.Name
            let meta = namedMeta d
            let typeVars = typeParameter @ d.TypeArgs
            [ Y.Class(dName, isTrait d, typeVars, classType @ d.ParentTraits, List.concat (memberDecl @ d.Members), meta) ]
        // removed in Dafny 4.2.0
        (* | :? OpaqueTypeDecl as d ->
            let dName = d.Name
            let meta = namedMeta d
            // Misuse Datatype for now when translating opaque types
            let typeVars = typeParameter @ d.TypeArgs
            [ Y.Datatype(dName, typeVars, [], List.concat (memberDecl @ d.Members), meta) ] *)
        | :? ModuleExportDecl as d ->
            let exportPath (expSig: ExportSignature) =
                match expSig.Decl with
                | :? MemberDecl as md -> Some(pathOfMemberDecl md)
                | :? TypeSynonymDecl as sd -> Some(Y.Path [ sd.Name ])
                | :? IndDatatypeDecl as dd -> Some(pathOfTopLevelDecl dd)
                | :? AliasModuleDecl as ad -> Some(pathOfTopLevelDecl ad)
                | _ -> None

            let exports = d.Exports |> List.ofSeq

            let provides, reveals =
                List.fold
                    (fun (provides, reveals) (expSig: ExportSignature) ->
                        match expSig.Opaque, exportPath expSig with
                        | true, Some ps -> ps :: provides, reveals
                        | false, Some ps -> provides, ps :: reveals
                        | _, _ (* cannot handle *)  -> provides, reveals)
                    ([], [])
                    exports

            [ Y.Export(Y.ExportType(provides, reveals)) ]
        | _ ->
            // default module contains a default class, which contains non-nesting declarations
            unsupported (
                "Toplevel declaration "
                + td.Name
                + " of type "
                + td.GetType().FullName
            )

    and constructorDecl (c: DatatypeCtor) : Y.DatatypeConstructor =
        let cName = c.Name

        { name = cName
          ins = formal @ c.Formals
          meta = namedMeta c }

    and case (e: MatchCase) : Y.Case =
        let vardecls = boundVar @ e.Arguments

        let bd =
            match e with
            | :? MatchCaseExpr as c -> expr c.Body
            | :? MatchCaseStmt as c -> Y.EBlock(statement @ c.Body)
            | _ -> error "Unexpected match case"

        let p =
            pathOfTopLevelDecl(e.Ctor.EnclosingDatatype)
                .child (e.Ctor.Name)

        YIL.plainCase (p, vardecls, bd)

    and nestedCase (srcTp: Type) (e: NestedMatchCase) : Y.Case =
        let vardecls, patt = pattern srcTp e.Pat

        let bd =
            match e with
            | :? NestedMatchCaseExpr as c -> expr c.Body
            | :? NestedMatchCaseStmt as c -> Y.EBlock(statement @ c.Body)
            | _ -> error "Unexpected match case"

        { vars = vardecls
          patterns = patt
          body = bd }

    and pattern (srcTp: Type) (p: ExtendedPattern) : Y.LocalDecl list * Y.Expr list =
        match p with
        | :? LitPattern as p -> [], [ expr p.OrigLit ]
        | :? IdPattern as p ->
            if p.ResolvedLit <> null then
                [], [ expr p.ResolvedLit ]
            else if p.Arguments = null then
                [ Y.LocalDecl(p.Id, tp p.Type, false) ], [ Y.EVar(p.Id) ]
            else
                let dss, ps =
                    (pattern (srcTp) @ p.Arguments) |> List.unzip

                let n = p.Ctor.Name

                let patternT =
                    if n.StartsWith(DafnyTupleMake) then
                        Y.ETuple(List.concat ps)
                    else
                        let constr =
                            pathOfTopLevelDecl(p.Ctor.EnclosingDatatype)
                                .child (p.Ctor.Name)

                        let tpArgs = tp @ srcTp.NormalizeExpand().TypeArgs
                        Y.EConstructorApply(constr, tpArgs, List.concat ps)

                List.concat dss, [ patternT ]
        | :? DisjunctivePattern as p ->
            let dss, ps =
                (pattern (srcTp) @ p.Alternatives) |> List.unzip

            List.concat dss, List.concat ps
        | _ -> unsupported "unknown pattern"
    
    and casePattern (e: CasePattern<BoundVar>) : Y.LocalDecl list * Y.Expr =
        if e.Var = null then
            let vars, lhs = List.unzip (casePattern @ e.Arguments)
            List.concat vars, Y.ETuple lhs
        else
            let var = e.Var
            // use DisplayName to preserve "_"
            [ Y.LocalDecl(var.DisplayName, tp var.Type, false) ], Y.EVar var.DisplayName

    and casePatternLocalVariable (e: CasePattern<LocalVariable>) : Y.LocalDecl list * Y.Expr =
        if e.Var = null then
            let vars, lhs = List.unzip (casePatternLocalVariable @ e.Arguments)
            List.concat vars, Y.ETuple lhs
        else
            let var = e.Var
            // use DisplayName to preserve "_"
            [ Y.LocalDecl(var.DisplayName, tp var.Type, false) ], Y.EVar var.DisplayName

    and isTrait (d: TopLevelDecl) =
        match d with
        | :? TraitDecl -> true
        | _ -> false

    and methodType (isByMethod: bool, s: string) =
        match isByMethod, s with
        | _, Prefix "static " s2 -> methodType (isByMethod, s2)
        | _, Prefix "ghost " s2 -> methodType (isByMethod, s2)
        | true, "function" -> Y.IsFunctionMethod
        | false, "function" -> Y.IsFunction
        | _, "function method" -> Y.IsFunctionMethod
        | true, "predicate" -> Y.IsPredicateMethod
        | false, "predicate" -> Y.IsPredicate
        | _, "predicate method" -> Y.IsPredicateMethod
        | _, "least predicate" -> Y.IsLeastPredicate
        | _, "greatest predicate" -> Y.IsGreatestPredicate
        | _, "lemma" -> Y.IsLemma
        | _, "least lemma" -> Y.IsLeastLemma
        | _, "greatest lemma" -> Y.IsGreatestLemma
        | _, "method" -> Y.IsMethod
        | _ -> unsupported $"unsupported method type payload: %s{s}"

    and updateDeclByAttribute (e: Y.Decl) (attr: UserSuppliedAttributes): Y.Decl =
        let attributes =
            [ "axiom"
              "fuel"
              "java"
              "javainline"
              "rust"
              "rustinline"
              "tailrecursion" ]
        let args = fromIList attr.Args
        if List.contains attr.Name attributes then
            let v = if args.IsEmpty then [] else (List.map (fun f -> f.ToString()) args)
            e.updateMeta(e.meta.addAttribute(attr.Name, v))
        else
            match e with
            | Y.Method(methodType, name, tpvars, inputSpec, outputSpec, modifies, reads, decreases, body, ghost, isStatic, isOpaque, meta) ->
                match attr.Name, args with
                | "opaque", args when args.Length <= 1 ->
                    let isOpaqueNew = args.IsEmpty || LiteralExpr.IsTrue(args.Item(0))
                    Y.Method(methodType, name, tpvars, inputSpec, outputSpec, modifies, reads, decreases, body, ghost, isStatic, isOpaqueNew, meta)
                | _ ->
                    warning $"dropping unsupported attribute: %s{attr.Name} (%d{(fromIList attr.Args).Length} arguments)"
                    e
            | _ ->
                warning $"dropping unsupported attribute: %s{attr.Name} (%d{(fromIList attr.Args).Length} arguments)"
                e

    and updateDeclByAttributes (e: Y.Decl) (attr: Attributes): Y.Decl =
        match attr with
        | null -> e
        | :? UserSuppliedAttributes as u ->
            updateDeclByAttributes (updateDeclByAttribute e u) attr.Prev
        | _ ->
            let defaultAttributes =
                [ "fuel"
                  "_induction" ]
            if List.contains attr.Name defaultAttributes then
                updateDeclByAttributes e attr.Prev  // ignore this attribute
            else
                unsupported $"unsupported attributes: %s{attr.Name}"

    and memberDecl (m: MemberDecl) : Y.Decl list =
        let result =
            match m with
            | :? Constructor as m ->
                let tpvars = typeParameter @ m.TypeArgs

                let body =
                    if (m.Body = null) then
                        None
                    else
                        Some(statement m.Body)

                let mName = m.Name

                let input =
                    Y.InputSpec(formal @ m.Ins, condition @ m.Req)

                let output = condition @ m.Ens
                [Y.ClassConstructor(mName, tpvars, input, output, body, namedMeta m)]
            | :? Function as m ->
                // keywords function (ghost), function method, predicate (ghost)
                let tpvars = typeParameter @ m.TypeArgs

                let input =
                    Y.InputSpec(formal @ m.Formals, condition @ m.Req)

                let ensures = condition @ m.Ens

                let output =
                    // always a single output; m.Result is null if that output is unnamed
                    if m.Result <> null then
                        Y.OutputSpec([ formal m.Result ], ensures)
                    else
                        Y.outputType (tp m.ResultType, ensures)

                let modifies = [] // functions do not modify

                let reads =
                    List.ofSeq m.Reads
                    |> List.map (fun (e: FrameExpression) -> expr e.E)

                let decreases =
                    List.ofSeq m.Decreases.Expressions
                    |> List.map expr

                let body =
                    if (m.Body = null) then
                        None
                    else
                        Some(expr m.Body)

                let mName = m.Name
                let meta = namedMeta m

                let yilMethodType =
                    methodType (m.ByMethodDecl <> null, m.GetFunctionDeclarationKeywords(dafnyOptions))

                [ Y.Method(
                    yilMethodType,
                    mName,
                    tpvars,
                    input,
                    output,
                    modifies,
                    reads,
                    decreases,
                    body,
                    m.IsGhost,
                    m.IsStatic,
                    m.IsOpaque,
                    meta
                ) ]
            | :? Method as m ->
                // keywords method, lemma (ghost)
                let tpvars = typeParameter @ m.TypeArgs
                let ins = formal @ m.Ins
                let reqs = condition @ m.Req
                let input = Y.InputSpec(ins, reqs)
                let outs = formal @ m.Outs
                let ens = condition @ m.Ens
                let output = Y.OutputSpec(outs, ens)

                let modifies =
                    m.Mod.Expressions
                    |> List.ofSeq
                    |> List.map (fun (e: FrameExpression) -> expr e.E)

                let decreases =
                    m.Decreases.Expressions
                    |> List.ofSeq
                    |> List.map expr

                let body =
                    if (m.Body = null) then
                        None
                    else
                        Some(statement m.Body)

                let mName = m.Name

                let yilMethodType =
                    match m with
                    | :? Lemma -> Y.IsLemma
                    | _ -> Y.IsMethod

                if mName.StartsWith(DafnyReveal) then
                    []  // not written explicitly
                else
                    [Y.Method(
                        yilMethodType,
                        mName,
                        tpvars,
                        input,
                        output,
                        modifies,
                        [],
                        decreases,
                        body,
                        m.IsGhost,
                        m.IsStatic,
                        m.IsOpaque,
                        namedMeta m
                    )]
            | :? ConstantField as m ->
                let mName = m.Name
                let meta = namedMeta m

                let dfO =
                    if m.Rhs = null then
                        None
                    else
                        Some(expr m.Rhs)

                [Y.Field(mName, tp m.Type, dfO, m.IsGhost, m.IsStatic, isMutable = false, meta = meta)]
            | :? Field as m ->
                let mName = m.Name
                let meta = namedMeta m
                // Non-constant fields do not have a RHS in Dafny
                // They are always initialized in the `constructor`
                [Y.Field(mName, tp m.Type, None, m.IsGhost, m.IsStatic, isMutable = true, meta = meta)]
            | _ -> unsupported (m.ToString())
        List.map (fun d -> updateDeclByAttributes d m.Attributes) result

    and formal (f: Formal) : Y.LocalDecl =
        Y.LocalDecl(f.Name, tp f.Type, f.IsGhost)

    and typeParameter (t: TypeParameter) : Y.TypeArg =
        let v =
            match t.VarianceSyntax with
            | TypeParameter.TPVarianceSyntax.NonVariant_Strict -> ""
            | TypeParameter.TPVarianceSyntax.Covariant_Strict -> "+"
            | TypeParameter.TPVarianceSyntax.Contravariance -> "-"
            | TypeParameter.TPVarianceSyntax.Covariant_Permissive -> "*"
            | TypeParameter.TPVarianceSyntax.NonVariant_Permissive -> "!"
            | _ -> unsupported ("variance: " + t.ToString())

        let e =
            match t.Characteristics.EqualitySupport with
            | TypeParameter.EqualitySupportValue.Required -> true
            | _ -> false // InferedRequired?

        let h =
            t.Characteristics.ContainsNoReferenceTypes

        (t.Name, (v, e, h))

    and condition (a: AttributedExpression) : Y.Condition = (expr a.E, None)

    and tp (t: Type) : Y.Type =

        match t with
        | :? UserDefinedType as t ->
            // Detection of type parameters: https://github.com/dafny-lang/dafny/pull/1188
            match t.ResolvedClass with
            | :? TypeParameter -> Y.TVar(t.Name)
            | _ ->
                // NewTypeDecl, IndDatatypeDecl, TupleTypeDecl
                // ArrowTypeDecl, TraitDecl, SubsetTypeDecl, TypeSynonymDecl
                let p = pathOfUserDefinedType (t)
                let args = tp @ t.TypeArgs
                // the default treatment
                let makeTApply () =
                    let tT = Y.TApply(p, args)

                    if t.IsRefType && not t.IsNonNullRefType then
                        Y.TNullable tT
                    else
                        tT
                // translate common types in CommonTypes.dfy.
                // This is included both in JavaLib and RustLib.
                let tpCommon (t: UserDefinedType) n (args: YIL.Type list) err =
                    (match n with
                     | "int8" -> Y.TInt Y.Bound8
                     | "int16" -> Y.TInt Y.Bound16
                     | "int32" -> Y.TInt Y.Bound32
                     | "int64" -> Y.TInt Y.Bound64
                     | "float" -> Y.TReal Y.Bound32
                     | "double" -> Y.TReal Y.Bound64
                     | _ -> unsupported $"%s{err}: %s{t.ToString()}")
                // Dafny puts a few built-in types into the DafnySystem namespace instead of making them primitive
                if p.names.Head = DafnySystem then
                    let n = p.names.Item(1)

                    if n = "string" then
                        Y.TString Y.NoBound
                    elif n = "nat" then
                        Y.TNat Y.NoBound
                    elif n.StartsWith(DafnyArrayPrefix) then
                        if args.Length = 1 then
                            Y.TArray(Y.NoBound, n, args.Head)
                        else
                            error $"array {p.name} must have exactly one type argument"
                    elif
                        n.StartsWith(DafnyFun)
                        || n.StartsWith(DafnyTotalFun)
                        || n.StartsWith(DafnyPartialFun)
                    then
                        // _#FuncN where N is arity
                        // _#TotalFuncN where N is arity
                        // _#PartialFuncN where N is arity
                        let numIns = args.Length - 1
                        Y.TFun(args.GetSlice(Some 0, Some(numIns - 1)), args.Item(numIns))
                    elif n.StartsWith(DafnyTuple) then
                        // DafnyTuple + "N" where N is arity
                        Y.TTuple(args)
                    elif n = "object" then
                        // Only allowed in ghost code
                        Y.TObject
                    else
                        unsupported $"built-in type {n}"
                else
                    makeTApply ()
        (* we used to have all this special treatment for DafnyLib types, which was removed
                   code is kept while migrating to the new solution
                 elif p.names.Head = "TypeUtil" then
                    // Legacy: types defined by Yucca in TypeUtil.dfy
                    // This is only for legacy support, can be removed later if we don't run typeCart on a
                    // legacy diff.
                    let n = p.names.Item(1)
                    (p, begin match n with
                        | "string32" -> Y.TString Y.Bound32
                        | "seq32" when args.Length = 1 -> Y.TSeq(Y.Bound32, args.Head)
                        | "set32" when args.Length = 1 -> Y.TSet(Y.Bound32, args.Head)
                        | "map32" when args.Length = 2 -> Y.TMap (Y.Bound32, args.Head, args.Tail.Head)
                        | "arr32" when args.Length = 1 -> Y.TArray(Y.Bound32, args.Head)
                        | "byteArray" -> Y.TArray(Y.NoBound, Y.TInt Y.Bound8)
                        | "nat32" -> Y.TNat Y.Bound32
                        | "nat64" -> Y.TNat Y.Bound64
                        | _ -> tpCommon t n args ("unknown type in TypeUtil")
                        end) |> Y.TApplyPrimitive
                elif p.names.Head = "JavaLib" then
                    // types defined by Yucca in JavaLib.dfy.
                    let n = p.names.Item(1)
                    (p, begin match n with
                        | "nat31" -> Y.TNat Y.Bound31
                        | "nat63" -> Y.TNat Y.Bound63
                        | "string31" -> Y.TString Y.Bound31
                        | "seq31" when args.Length = 1 -> Y.TSeq(Y.Bound31, args.Head)
                        | "arr31" when args.Length = 1 -> Y.TArray(Y.Bound31, args.Head)
                        | "map31" when args.Length = 2 -> Y.TMap(Y.Bound31, args.Head, args.Tail.Head)
                        | "set31" when args.Length = 1 -> Y.TSet(Y.Bound31, args.Head)
                        | "Option" when args.Length = 1 -> makeTApply()
                        // types in CommonTypes.dfy are included in JavaLib.dfy.
                        | _ -> tpCommon t n args ("unknown type in JavaLib")
                        end) |> Y.TApplyPrimitive
                else if p.names.Head = "rust_lib" then
                    // types defined by Yucca in rust_lib.dfy.
                    let n = p.names.Item(1)
                    (p, begin match n with
                        | "nat32" -> Y.TNat Y.Bound32
                        | "nat64" -> Y.TNat Y.Bound64
                        | "isize" -> Y.TInt Y.Bound64 // isize = int64
                        | "usize" -> Y.TNat Y.Bound64 // usize = nat64
                        | "string64" -> Y.TString Y.Bound64
                        | "seq64" when args.Length = 1 -> Y.TSeq(Y.Bound64, args.Head)
                        | "arr64" when args.Length = 1 -> Y.TArray(Y.Bound64, args.Head)
                        | "map64" when args.Length = 2 -> Y.TMap(Y.Bound64, args.Head, args.Tail.Head)
                        | "set64" when args.Length = 1 -> Y.TSet (Y.Bound64, args.Head)
                        // Recursive translation of RefL<T, L> = T, Ref<T> = T, Box<T> = T.
                        | "RefL" | "Ref" | "Box" -> makeTApply()
                        | _ -> tpCommon t n args ("unknown type in rust_lib")
                        end) |> Y.TApplyPrimitive
                elif p.names.Head = "CommonTypes" then
                    (p, if p.names.Item(1).StartsWith("Option") then
                            makeTApply()
                        else tpCommon t (p.names.Item(1)) args ("unknown type in CommonTypes"))
                    |> Y.TApplyPrimitive *)
        | :? BoolType -> Y.TBool
        | :? CharType -> Y.TChar
        | :? IntType -> Y.TInt Y.NoBound
        | :? RealType -> Y.TReal Y.NoBound
        | :? SetType as t -> Y.TSet(Y.NoBound, tp t.Arg)
        | :? SeqType as t ->
            let aT = tp t.Arg
            // Dafny treats string as seq<char> and sometimes expands it
            if aT = Y.TChar then
                Y.TString Y.NoBound
            else
                Y.TSeq(Y.NoBound, tp t.Arg)
        | :? MapType as t -> Y.TMap(Y.NoBound, tp t.Domain, tp t.Range)
        | :? TypeProxy as t -> tp t.T // e.g., wrapper for inferred types
        | :? BitvectorType as t -> Y.TBitVector(t.Width)
        | _ -> unsupported $"Type {t.ToString()}"

    and parseExprDotName (e: ExprDotName) : Y.Path option =
        match e.Lhs with
        | :? NameSegment as lhsName -> Some(Y.Path [ lhsName.Name; e.SuffixName ])
        | :? ExprDotName as lhsExpr ->
            let lhs = parseExprDotName lhsExpr

            if lhs.IsNone then
                None
            else
                Some(lhs.Value.child (e.SuffixName))
        | _ ->
            // TODO: more types
            None

    and replacePath (e: Y.Expr) (p: Y.Path option) : Y.Expr =
        if p.IsNone then
            e
        else
            Y.replacePath (e, p.Value)

    and exprO (e: Expression) : Y.Expr option =
        if e = null then
            None
        else
            Some(expr (e))

    and expr (e: Expression) : Y.Expr =
        match e with
        // case: `var foo :- MonadicExpr;` in function methods
        // LetOrFailExpr is a subtype of ConcreteSyntaxExpression, so we need to pattern match on this case before
        // LetOrFailExpr desugars to LetExpr (i.e. e.ResolvedExpression is a LetExpr), so we lose the information
        // about the if-then-else structure by doing that.
        | :? LetOrFailExpr as e ->
            match e.ResolvedExpression with
            | :? LetExpr as e ->
                let rhs = expr @ e.RHSs

                match e.Body with
                | :? ITEExpr as iteE ->
                    let elseExpr = (iteE.Els :?> LetExpr)
                    let vars, lhs = List.unzip (casePattern @ elseExpr.LHSs)
                    let body = expr (elseExpr.Body)
                    Y.ELet(List.concat vars, e.Exact, true, lhs, rhs, body)
                | _ -> error "LetOrFailExpr must have an ITEExpr"
            | _ -> error "LetOrFailExpr always resolves to LetExpr"
        // NameSegment is a subtype of ConcreteSyntaxExpression
        | :? NameSegment as e ->
            Y.EVar(e.Name)
        | :? ConcreteSyntaxExpression as e ->
            // cases that are eliminated during resolution
            if e.ResolvedExpression = null then
                match Seq.head e.Children with
                | :? ConcreteSyntaxExpression as e_child ->
                    if e_child.ResolvedExpression = null then
                        Y.EUnimplemented
                    else
                        expr e_child.ResolvedExpression
                | _ -> Y.EUnimplemented // a few expressions are not resolved by Dafny
            else
                expr e.ResolvedExpression
        // identifiers/names
        | :? IdentifierExpr as e -> Y.EVar(e.Var.Name)
        | :? MemberSelectExpr as e ->
            let r = receiver (e.Obj.Resolved)
            let p = pathOfMemberDecl (e.Member)

            if p.names.Item(0) = DafnySystem then
                let e =
                    match r with
                    | Y.ObjectReceiver (e) -> e
                    | Y.StaticReceiver _ -> error "Unknown receiver"

                if p.names.Item(1).StartsWith(DafnyTuple) then
                    let i = p.name |> int
                    Y.EProj(e, i)
                elif p.names.Item(1) = DafnyMap
                     && p.names.Item(2) = DafnyKeys then
                    Y.EMapKeys(e)
                elif p.names.Item(1) = DafnyMap
                     && p.names.Item(2) = DafnyValues then
                    Y.EMapValues(e)
                elif p.names.Item(1).StartsWith(DafnyFun)
                     && p.names.Item(2) = DafnyReads then
                    Y.EMemberRef(r, p, [])
                elif
                    p.names.Item(1).StartsWith(DafnyArrayPrefix)
                    && p.names.Item(2).StartsWith("Length")
                then
                    Y.EMemberRef(r, p, [])
                else
                    unsupported $"Unknown member {p}"
            else
                let tpargs = tp @ e.TypeApplication_AtEnclosingClass
                // const field vs field
                let isPrivate = e.Member.WhatKind.Equals("field")
                if p.name.StartsWith(DafnyReveal) then  // remove "reveal_" prefix and append "()"
                    Y.EAnonApply(Y.EMemberRef(r, p.parent.child(p.name[DafnyReveal.Length..]), tpargs), [])
                else
                    Y.EMemberRef(r, p, tpargs)
        | :? ThisExpr -> Y.EThis
        // literals
        | :? CharLiteralExpr as e -> Y.EChar(string e.Value) // always a string according to Dafny spec
        | :? StringLiteralExpr as e -> Y.EString(string e.Value) // always a string according to Dafny spec
        | :? LiteralExpr as e ->
            // superclass of the above, so must come last
            match e.Value with
            | :? bool as v -> Y.EBool(v)
            | :? BigInteger as v -> Y.EInt(v, tp e.Type)
            | :? BigDec as v -> Y.EReal(v, tp e.Type)
            | null ->
                // StaticReceiverExpr lands here if it is not handled earlier
                Y.ENull(tp e.Type)
            | _ -> unsupported $"Literal value {e.ToString()}"
        | :? LambdaExpr as e ->
            let vars = boundVar @ e.BoundVars
            let cond = if e.Range = null then None else Some(expr e.Range, None)
            Y.EFun(vars, cond, tp e.Body.Type, expr e.Body)
        | :? SeqSelectExpr as e -> Y.ESeqSelect(expr e.Seq, tp e.Seq.Resolved.Type, e.SelectOne, exprO e.E0, exprO e.E1)
        | :? MultiSelectExpr as e ->
            // TODO check if this can occur for anything but multi-dimensional arrays
            Y.EMultiSelect(expr e.Array, expr @ e.Indices)
        | :? SeqDisplayExpr as e ->
            let elems = expr @ e.Elements

            match tp e.Type with
            // empty string literal sometimes presents as empty char sequence
            | Y.TString _ when List.isEmpty elems -> Y.EString ""
            | Y.TString _ -> Y.EToString elems
            | Y.TSeq (_, a) -> Y.ESeq(a, elems)
            | _ -> unsupported (sprintf "unexpected sequence type: %s" ((tp e.Type).ToString()))
        | :? SeqUpdateExpr as e -> Y.ESeqUpdate(expr e.Seq, expr e.Index, expr e.Value)
        // applications
        | :? FunctionCallExpr as e ->
            let r = e.Receiver
            let recv = receiver (r.Resolved)
            let args = expr @ e.Args

            let tpargs =
                // e.TypeApplication_AtEnclosingClass: type arguments for the datatype, not part of concrete syntax
                tp @ e.TypeApplication_JustFunction

            Y.EMethodApply(recv, pathOfMemberDecl (e.Function), tpargs, args, false)
        | :? ApplyExpr as e -> Y.EAnonApply(expr e.Function, expr @ e.Args)
        | :? UnaryOpExpr as e ->
            let o = e.Op.ToString()
            // disambiguate Dafny's ad-hoc polymorphism
            Y.EUnOpApply(o, expr e.E)
        | :? BinaryExpr as e ->
            let o = e.ResolvedOp.ToString()
            Y.EBinOpApply(o, expr e.E0, expr e.E1)
        | :? DatatypeValue as e ->
            let ctor = e.Ctor
            let n = ctor.Name
            // we assume constructor names live in the scope of the containing datatype
            // Dafny's FullName function actually prefixes them with "#"
            let path =
                pathOfTopLevelDecl(ctor.EnclosingDatatype)
                    .child (n)

            let tpargs = tp @ e.InferredTypeArgs
            let args = expr @ e.Arguments

            if n.StartsWith(DafnyTupleMake) then
                Y.ETuple(args) // tpargs are the types of the components
            else
                if n.Contains("#") then
                    // make sure we caught all the built-in names
                    unsupported $"special name: {n}"

                Y.EConstructorApply(path, tpargs, args)
        // others
        | :? ConversionExpr as e -> Y.ETypeConversion(expr e.E, tp e.ToType)
        | :? TypeTestExpr as e -> Y.ETypeTest(expr e.E, tp e.ToType)
        | :? StmtExpr as e ->
            // S;E
            Y.EBlock([ statement e.S; expr e.E ])
        | :? LetExpr as e ->
            let vars, lhs = List.unzip (casePattern @ e.LHSs)
            let rhs = expr @ e.RHSs
            Y.ELet(List.concat vars, e.Exact, false, lhs, rhs, expr e.Body)
        | :? ITEExpr as e -> Y.EIf(expr e.Test, expr e.Thn, Some(expr e.Els))
        | :? MatchExpr as e -> Y.EMatch(expr e.Source, tp e.Source.Type, case @ e.Cases, None)
        | :? NestedMatchExpr as e ->
            Y.EMatch(expr e.Source, tp e.Source.Type, nestedCase (e.Source.Type) @ e.Cases, None)
        | :? QuantifierExpr as e ->
            // mostly in logic parts; but can only be computational if domain is finite (occurs once in Yucca)
            // if e.TypeArgs > 0 then
            // Dafny quantifiers can only have type args when using the attribute `{:typeQuantifier}`,
            // https://github.com/dafny-lang/dafny/blob/288cab1c53eefbddaf13e2f8fb60eda394f87aa8/Source/Dafny/AST/DafnyAst.cs#L11481
            //    unsupported "quantifier with type arguments"

            let q =
                match e with
                | :? ForallExpr -> Y.Forall
                | :? ExistsExpr -> Y.Exists
                | _ -> error "unknown quantifier"

            Y.EQuant(q, boundVar @ e.BoundVars, exprO e.Range, expr e.Term)
        | :? OldExpr as e -> Y.EOld(expr e.E)
        | :? MapComprehension as e ->
            if not e.Finite then
                unsupported "map type must be finite"

            let tL =
                match e.TermLeft with
                | null -> None
                | exprL -> Some(expr exprL)

            let tR = expr e.Term

            let lds =
                e.BoundVars |> List.ofSeq |> List.map boundVar

            let rangePredicate = expr e.Range
            Y.EMapComp(lds, rangePredicate, tL, tR)
        | :? MapDisplayExpr as e ->
            if not e.Finite then
                unsupported "map type must be finite"

            let mapElts = e.Elements |> List.ofSeq

            let mapDisplay =
                List.fold
                    (fun l (p: ExpressionPair) ->
                        let keyTrans = expr p.A
                        let valTrans = expr p.B
                        (keyTrans, valTrans) :: l)
                    []
                    mapElts

            Y.EMapDisplay mapDisplay
        | :? SetComprehension as e ->
            if not e.Finite then
                unsupported "set comprehension must be finite"

            let lds =
                e.BoundVars |> List.ofSeq |> List.map boundVar

            let rangePredicate = expr e.Range
            let body = expr e.Term
            Y.ESetComp(lds, rangePredicate, body)
        | :? SetDisplayExpr as e ->
            if not (e.Finite) then
                unsupported "Infinite set definition"

            let elems = expr @ e.Elements

            let t =
                match (tp e.Type) with
                | Y.TSet (_, a) -> a
                | _ -> error "Unexpected set type"

            Y.ESet(t, elems)
        | :? SeqConstructionExpr as e ->
            let seqtp = tp e.Type

            let elemtp =
                match seqtp with
                | Y.TSeq (_, a) -> a
                | a -> unsupported ("unexpected sequence type: " + a.ToString())

            Y.ESeqConstr(elemtp, expr e.N, expr e.Initializer)
        | null -> error "expression is null"
        | _ -> unsupported ("expression " + e.ToString())

    and statement (s: Statement) : Y.Expr =
        match s with
        // removed in Dafny 4
        // | :? ConcreteSyntaxStatement as s ->
        //    // cases that are eliminated during resolution
        //    statement s.ResolvedStatement
        | :? BlockStmt as b -> Y.EBlock(statement @ b.Body)
        | :? NestedMatchStmt as e ->
            Y.EMatch(expr e.Source, tp e.Source.Type, nestedCase (e.Source.Type) @ e.Cases, None)
        | :? VarDeclStmt as s ->
            let vs = boundVar @ s.Locals
            let lhs = (fun (v: LocalVariable) -> Y.EVar v.DisplayName) @ s.Locals

            match s.Update with
            | null -> Y.EDecls(vs, lhs, [])
            | :? UpdateStmt as u ->
                // Rewrite var _, _ := rhs1, rhs2 to rhs1; rhs2
                if List.forall (fun (x: LocalVariable) -> x.DisplayName = "_") (fromIList s.Locals) then
                    let ds = rhsOfUpdate (u)

                    let blockS =
                        List.map (fun (x: Y.UpdateRHS) -> x.df) ds

                    match blockS with
                    | [] -> error "RHS expected for var _ := ... statement"
                    | [ s ] -> s
                    | _ -> Y.EBlock(blockS)
                else
                    let ds = rhsOfUpdate (u)

                    if vs.Length <> ds.Length then
                        error "Number of LHSs in variable declaration does not match number of RHSs"

                    Y.EDecls(vs, lhs, ds)
            | :? AssignSuchThatStmt as u ->
                if vs.Length <> 1 then
                    unsupported "Variable declaration with more than 1 LHS"

                let v = vs.Head
                let c = expr u.Expr
                Y.EDeclChoice(v, c)
            | :? AssignOrReturnStmt as u ->
                (* See the comment on the case for AssignOrReturnStmt in the method 'statement'
                  This is just the special case where a monadic value is used to initialize a variable *)
                if vs.Length <> 1 then
                    unsupported "Variable declaration with more than 1 LHS"

                let d = rhsOfMonadicUpdate u
                Y.EDecls(vs, lhs, [ d ])
            | _ -> unsupported "Non-trivial RHS in variable declaration"
        | :? UpdateStmt as s ->
            (* general form is pattern, ..., pattern := value, ..., value
                Lengths need not be the same: RHS can be single expression evaluating to sequence (e.g., method call).
                usually resolves into an AssignStmt or a CallStmt, which seem to occur only after resolution
                the former has a single expression (i.e., pattern on the LHS)
                the latter has a single method call on the RHS, but may have multiple LHS *)
            let res = fromIList s.ResolvedStatements

            if res.Length = 1 then
                statement (res.Item(0))
            else
                (* Presumably this is what happens to more complex updates
                   we could handle this too, but it's good to first see if and how it occurs before deciding how to handle it *)
                unsupported "Update statement with complex resolution"
        | :? CallStmt as s ->
            // pattern, ..., pattern := receiver.method(args)
            // the RHS is easy
            let r = receiver (s.Receiver.Resolved)
            let meth = s.MethodSelect

            let tpargs =
                List.append (tp @ meth.TypeApplication_AtEnclosingClass) (tp @ meth.TypeApplication_JustMember)

            let args = expr @ s.Args
            let ghost = s.Method.IsGhost // true if this is a lemma call

            let rhs =
                Y.EMethodApply(r, pathOfMemberDecl (s.Method), tpargs, args, ghost)
            (* the LHS is a bit more complicated
              The only case we allow is name, g1, ..., gn := value,
              where the gi are ghost variables. If n!=0, the value must be a method call returning n+1 values,
              of which all but the first are ghosts - see the comment on translating method declarations.
            *)
            let ls = fromIList s.Lhs

            if s.Lhs.Count = 0 then
                rhs
            else
                let lhsIsGhost (e: Expression) : bool =
                    match e.Resolved with
                    | :? IdentifierExpr as r -> r.Var.IsGhost
                    | _ -> false

                let onlyOneNonGhost = List.forall lhsIsGhost ls.Tail

                if not onlyOneNonGhost then
                    unsupported "Variable update with more than one non-ghost LHS"
                else
                    let doOne (e: Expression) =
                        match e with
                        // plain assignment name := value
                        | :? IdentifierExpr as l -> expr l
                        | :? MemberSelectExpr as e -> expr e
                        // complex assignment pattern := value
                        | _ -> unsupported "Variable declaration with non-atomic LHS"

                    let ns = List.map doOne ls
                    Y.EUpdate(ns, { df = rhs; monadic = None })
        | :? AssignStmt as s ->
            let rhs = assignmentRhs (s.Rhs)

            match s.Lhs with
            | :? IdentifierExpr as e -> Y.EUpdate([ expr e ], { df = rhs; monadic = None })
            | :? SeqSelectExpr as e ->
                (* TODO check if this is true: We assume this case always means an array update.
                   We only support one-dimensional case a[i] := e for now
                   This only occurs once in Yucca, albeit in string comparison where efficiency may be critical.
                 *)
                match e.Seq.Resolved with
                | :? IdentifierExpr as s -> Y.EArrayUpdate(Y.EVar(s.Name), [ expr e.E0 ], rhs)
                | _ -> unsupported "Complex sequence update"
            | :? MemberSelectExpr as e -> Y.EUpdate([ expr e ], { df = rhs; monadic = None })
            | :? MultiSelectExpr as e ->
                (* TODO use EArrayUpdate *)
                Y.EUpdate([ Y.EMultiSelect(expr e.Array, expr @ e.Indices) ], { df = rhs; monadic = None })
            | _ -> unsupported "Non-atomic LHS of assignment"
        | :? VarDeclPattern as s ->
            (* Because we do not cover constructor patterns anyway, we can simply use a Decl to represent a let statement.
               These statements (only?) occur when a match statement is rewritten during resolution
               They are used to declare the pattern variables and bind them to the matched subexpressions
               (which are themselves generated variables).
            *)
            let v = s.LHS
            let vars, lhs = casePatternLocalVariable v
            Y.EDecls(vars, [ lhs ], [ { df=expr s.RHS; monadic=None } ])
        | :? ReturnStmt as s ->
            (* There may be more than one return value - see the comment on the translation of the method header.
               There may be no or multiple return values - see the comment on EReturn. *)
            let rs = s.Rhss

            let es =
                if rs = null then
                    [] // no return value; it seems rs is never the empty list
                else
                    let doOne (r: AssignmentRhs) =
                        match r with
                        | :? ExprRhs as r -> expr r.Expr
                        | _ -> unsupported "Non-trivial return statement"

                    doOne @ rs

            Y.EReturn(es)
        | :? AssignOrReturnStmt as s ->
            (* name [: A] :- value, monadic assignment that propagates
               user-defined in the respective user-written monad datatype (here: Result).
               In anticipation of the translation, we use the original statement and not s.ResolvedStatements.
               See also the case for VarDeclStmt, which must be treated analogously.
            *)
            let u = rhsOfMonadicUpdate (s)

            let n =
                match s.Lhss.Count with
                | 0 ->
                    // :- v is monadic return v, never used in Yucca
                    unsupported "Empty LHS of :- statement"
                | 1 ->
                    // bind n :- v
                    match s.Lhss.Item(0) with
                    | :? NameSegment as l -> Y.EVar(l.Name)
                    | _ -> unsupported "Non-atomic LHS of :- statement"
                | _ -> unsupported "Multiple LHSs in :- statement"

            Y.EUpdate([ n ], u)
        | :? IfStmt as s ->
            if s.IsBindingGuard then
                unsupported "if statement used as binding guard"

            let els =
                if s.Els = null then
                    None
                else
                    Some(statement s.Els)

            Y.EIf(expr s.Guard, statement s.Thn, els)
        | :? AlternativeStmt as s ->
            let alternativeCase (case: GuardedAlternative) =
                if case.IsBindingGuard then
                    unsupported "alternative statement used as binding guard"

                (expr case.Guard, Y.EBlock(statement @ case.Body))

            Y.EAlternative(List.unzip (alternativeCase @ s.Alternatives))
        | :? WhileStmt as s -> Y.EWhile(expr s.Guard, statement s.Body, None)
        | :? ForLoopStmt as s -> Y.EFor(boundVar s.LoopIndex, expr s.Start, expr s.End, s.GoingUp, statement s.Body)
        | :? BreakStmt as s ->
            if s.TargetLabel <> null then // this used to check for s.BreakCount > 1
                unsupported "Non-trivial break statement"

            Y.EBreak None
        | :? MatchStmt as s -> Y.EMatch(expr s.Source, tp s.Source.Type, case @ s.Cases, None)
        | :? PrintStmt as s -> Y.EPrint(expr @ s.Args)
        | :? AssertStmt as s ->
            let proof =
                if s.Proof = null then
                    None
                else
                    Some(statement s.Proof)
            Y.EAssert(expr s.Expr, proof)
        | :? AssumeStmt as s -> Y.EAssume(expr s.Expr)
        | :? ExpectStmt as s -> Y.EExpect(expr s.Expr)
        | :? CalcStmt -> Y.ECommented("calculational proof omitted", Y.ESKip)
        | :? RevealStmt as s ->
            let rs = expr @ s.Exprs

            if List.contains YIL.EUnimplemented rs then
                warning "dropping unresolved reveal expression"

            let rs2 =
                rs
                |> List.filter (fun x -> x <> YIL.EUnimplemented)

            Y.EReveal rs2
        | :? ForallStmt as s ->
            // TODO: compile foralls correctly by also considering ensures clause
            Y.EQuant(
                Y.Forall,
                boundVar @ s.BoundVars,
                exprO s.Range,
                if s.Body <> null then
                    statement s.Body
                else
                    Y.ESKip
            )
        | :? SkeletonStatement -> Y.EUnimplemented (* '...;' skeleton statements *)
        | _ -> unsupported $"statement {s.ToString()}"
    // ***** qualified names; Dafny has methods for this, but they are a bit confusing and work with .-separated strings
    and pathOfModule (d: ModuleDefinition) : Y.Path =
        if d = null || d.IsDefaultModule then
            Y.Path([])
        else
            pathOfModule(d.EnclosingModule).child (d.Name)

    and pathOfTopLevelDecl (d: TopLevelDecl) : Y.Path =
        let p =
            pathOfModule (d.EnclosingModuleDefinition)

        match d with
        | :? DefaultClassDecl -> p
        | _ -> p.child (d.Name)

    and pathOfMemberDecl (d: MemberDecl) : Y.Path =
        pathOfTopLevelDecl(d.EnclosingClass)
            .child (d.Name)

    and pathOfUserDefinedType (u: UserDefinedType) : Y.Path = pathOfTopLevelDecl (u.ResolvedClass)

    // ***** auxiliary translation functions
    and boundVar (bv: IVariable) : Y.LocalDecl =
        Y.LocalDecl(bv.DisplayName, tp bv.Type, bv.IsGhost)

    and classType (t: Type) : Y.ClassType =
        match t with
        | :? UserDefinedType as u ->
            let p = pathOfUserDefinedType (u)
            let ts = tp @ u.TypeArgs
            { path = p; tpargs = ts }
        | _ -> error "unknown type"

    and receiver (r: Expression) : Y.Receiver =
        match r with
        | :? StaticReceiverExpr as r ->
            let ct = classType (r.Type)
            Y.StaticReceiver(ct)
        | _ -> Y.ObjectReceiver(expr r)

    and unqualifyReceiver (recv: Y.Receiver) : Y.Receiver =
        match recv with
        | Y.StaticReceiver s ->
            if s.path.names.Length >= 2 then
                Y.StaticReceiver
                    { path = Y.Path [ s.path.name ]
                      tpargs = s.tpargs }
            else
                recv
        | _ -> recv

    and assignmentRhs (r: AssignmentRhs) : Y.Expr =
        match r with
        | :? ExprRhs as r ->
            // name := value
            expr r.Expr
        | :? TypeRhs as r ->
            // name := new ...
            if r.ArrayDimensions <> null then
                // name := new A[dimensions]...
                let init: Y.ArrayInitializer =
                    if r.ElementInit <> null then
                        // name := new A[dimensions](initializer)
                        Y.ComprehensionLambda(expr r.ElementInit)
                    elif r.InitDisplay <> null then
                        // name := new A[dimension][values]
                        Y.ValueList(expr @ r.InitDisplay)
                    else
                        Y.Uninitialized
                Y.EArray(tp r.EType, expr @ r.ArrayDimensions, init)
            else
                (* This is not correct if anything but a default constructor is to be applied.
                   That is fine because in Yucca, this case only occurs for constructing iterators.
                *)
                let ct = classType (r.Type)

                let exprFromBinding (e: ActualBinding) = e.Actual

                let args =
                    List.map expr (exprFromBinding @ r.Bindings.ArgumentBindings)

                Y.ENew(ct, args)
        | _ -> unsupported "Non-trivial RHS in update"
    (* Dafny stores the RHS of a variable declaration or an update in an update statement
       The RHS in there does not get resolved though.
       Instead, the entire statement is resolved into another statement.
       So we translate that statement and then extract the RHS from it.
       If there are multiple LHSs, there should also be multiple RHSs, so we return a list.
    *)
    and rhsOfUpdate (u: UpdateStmt) : Y.UpdateRHS list =
        let doOne (s: Statement) : Y.UpdateRHS =
            match statement (s) with
            | Y.EUpdate (_, e) -> e
            | _ -> error "unexpected update"

        doOne @ u.ResolvedStatements
    (* for a monadic RHS, it's even trickier: the statement gets resolved into three statements,
       the first of which contains a variable declaration, whose update statement has the needed RHS *)
    and rhsOfMonadicUpdate (ar: AssignOrReturnStmt) : Y.UpdateRHS =
        let res = fromIList ar.ResolvedStatements

        match res with
        | [ :? VarDeclStmt as v; :? UpdateStmt as u; :? IfStmt; :? UpdateStmt ]
        | [ :? VarDeclStmt as v; :? UpdateStmt as u; :? AssertStmt; :? UpdateStmt ] ->
            let ds = rhsOfUpdate (u)

            if ds.Length <> 1 then
                error "Unexpected number of RHSs in update"

            let d = ds.Head.df
            let t = (boundVar @ v.Locals).Head.tp
            { df = d; monadic = Some(t) }
        | _ -> error "Unexpected resolution"
