namespace TypeInjections

open System
open TypeInjections.Diff
open TypeInjections.YIL

/// Wrappers for standard Dafny functions that we assume to exist; need to be written and added to yucca
module DafnyFunctions =
    let rcv p =
        StaticReceiver { path = p; tpargs = [] }

    let fb =
        Path [ "Translations"
               "MapBuiltinTypes" ]

    let rcvFunc = rcv fb
    let utils = rcv (Path [ "Translations"; "Utils" ])
    /// given translation t: o -> n,
    /// return element-wise translation: seq<o> -> seq<n>
    let seqRel o n t e =
        EMethodApply(rcvFunc, fb.child ("Seq"), [ o; n ], [ t; e ], false)
    /// given translation t: o -> n,
    /// return element-wise translation: arr<o> -> arr<n>
    let arrayRel o n t e =
        EMethodApply(rcvFunc, fb.child ("Array"), [ o; n ], [ t; e ], false)
    /// given translation t: o -> n,
    /// return element-wise translation: set<o> -> set<n>
    let setRel o n t e =
        EMethodApply(rcvFunc, fb.child ("Set"), [ o; n ], [ t; e ], false)
    /// given translations sT1: sO -> sN, sT2: sN -> sO, tT1: tO -> tN, tT2: tN -> tO,
    /// return translation: map<sO, tO> -> map<sN, tN> for each element e in sN with a preimage in sT1
    let mapRel sO sN (sT1, sT2) tO tN (tT1, tT2) e =
        EMethodApply(rcvFunc, fb.child ("Map"), [ sO; sN; tO; tN ], [ sT1; sT2; tT1; e ], false)
    /// ???()
    let missingTerm =
        EMethodApply(utils, fb.child ("???"), [], [], false)

open DafnyFunctions

// variable naming conventions:
//  xD: diff between two x's
//  xT: translation of x

/// takes a diff between two YIL objects and returns the translation declarations/objects for it
module Translation =
    let unsupported s = "unsupported: " + s
    /// config for translator
    type TranslatorConfig =
        { // If we want to generate lemmas even if the function/method is not affected by the change.
          alwaysGenerateLemmas: bool

          // If we want to generate axioms for functions not affected by the change and called by functions
          // affected by the change. alwaysGenerateLemmas and generateAxiomsForUnchanged should not both be true.
          generateAxiomsForUnchanged: bool 

          // If we want to expand all function arguments' requirements by one level from lambda expressions
          // to forall expressions.
          useForallInFunctionRequires: bool

          // If we want to expand all ensure statements of function return values by one level from function
          // equivalence to forall expressions.
          useForallInFunctionEnsures: bool

          // Set this variable to false only when no function types (higher-order functions) are used
          // to reduce the number of functions and variables that Dafny must consider.
          generateBackwardTranslationFunctions: bool
          
          // If we want to generate the proof sketch (if false, do not generate anything in the lemma body)
          generateProof: bool
          
          // In the proof sketch, we want to generate assertions at the leaf level of the AST (true)
          // or generate a single assertion (false)
          expandAssertions: bool
          
          // In the proof sketch, if we want to prepend lemma calls
          generateLemmaCalls: bool
          
          // If we want to generate a separate lemma for each higher-order function invocation with a
          // changed function argument
          specializeHigherOrderLemmas: bool
        }
    let defaultConfig =
        { alwaysGenerateLemmas = false
          generateAxiomsForUnchanged = true
          useForallInFunctionRequires = true
          useForallInFunctionEnsures = true
          generateBackwardTranslationFunctions = true
          generateProof = true
          expandAssertions = true
          generateLemmaCalls = true
          specializeHigherOrderLemmas = true }
    let stringToBool (value: string) =
        match Boolean.TryParse(value) with
        | true, b -> b
        | _ -> failwith "expected \"true\" or \"false\""
    let parseConfig (argvList: string list) =
        { alwaysGenerateLemmas =
              if List.exists (fun s -> s = "-a") argvList then
                  match List.item ((List.findIndex (fun s -> s = "-a") argvList) + 1) argvList with
                  | "1" -> true
                  | _ -> false
              else
                  defaultConfig.alwaysGenerateLemmas
          generateAxiomsForUnchanged =
              if List.exists (fun s -> s = "-a") argvList then
                  match List.item ((List.findIndex (fun s -> s = "-a") argvList) + 1) argvList with
                  | "2" -> true
                  | _ -> false
              else
                  defaultConfig.generateAxiomsForUnchanged
          useForallInFunctionRequires =
              if List.exists (fun s -> s = "-f") argvList then
                  List.item ((List.findIndex (fun s -> s = "-f") argvList) + 1) argvList |> stringToBool
              else
                  defaultConfig.useForallInFunctionRequires
          useForallInFunctionEnsures =
              if List.exists (fun s -> s = "-f") argvList then
                  List.item ((List.findIndex (fun s -> s = "-f") argvList) + 1) argvList |> stringToBool
              else
                  defaultConfig.useForallInFunctionEnsures
          generateBackwardTranslationFunctions =
              if List.exists (fun s -> s = "-b") argvList then
                  List.item ((List.findIndex (fun s -> s = "-b") argvList) + 1) argvList |> stringToBool
              else
                  defaultConfig.generateBackwardTranslationFunctions
          generateProof = defaultConfig.generateProof
          expandAssertions = defaultConfig.expandAssertions
          generateLemmaCalls = defaultConfig.generateLemmaCalls
          specializeHigherOrderLemmas = defaultConfig.specializeHigherOrderLemmas }

    /// translates a program, encapsulates global data/state for use during translation
    type Translator
        (
            ctxO: Context,
            ctxN: Context,
            declsD: Diff.DeclList,
            jointDecls: Path list,
            changedDecls: Set<Path>,
            calledByChangedDecls: Set<Path>,
            specializedLemmas: Map<Path, Expr list>,
            config: TranslatorConfig
        ) =
        /// given p, produces the paths to p in OLD, NEW, and PROOFS
        // This is the only place that uses the literal prefix strings.
        let rec path (p: Path) : Path * Path * Path =
            // joint decls are the same in old and new version
            // the translation declaration is still generated because e.g.,
            // a joint type can be called with non-joint type parameters
            if isJoint p then
                (p.prefix "Joint", p.prefix "Joint", p)
            else
                (p.prefix "Old", p.prefix "New", p)
        /// p will become part of JOINT
        and isJoint (p: Path) : bool =
            List.exists (fun (j: Path) -> j.isAncestorOf p) jointDecls
        /// OLD and NEW type are equal and will become part of JOINT
        and isJointType (tO: Type, tN: Type) : bool =
            match tO, tN with
            | TApply (pO, argsO), TApply (pN, argsN) ->
                pO = pN && isJoint pO && argsO.Length = argsN.Length && List.forall isJointType (List.zip argsO argsN)
            | TSeq (bO, sO), TSeq (bN, sN)
            | TSet (bO, sO), TSet (bN, sN) ->
                bO = bN && isJointType (sO, sN)
            | TMap (bO, kO, vO), TMap (bN, kN, vN) ->
                bO = bN && isJointType (kO, kN) && isJointType (vO, vN)
            | TArray (bO, nO, sO), TArray (bN, nN, sN) ->
                bO = bN && nO = nN && isJointType (sO, sN)
            | TNullable sO, TNullable sN ->
                isJointType (sO, sN)
            | TTuple tsO, TTuple tsN ->
                tsO.Length = tsN.Length && List.forall isJointType (List.zip tsO tsN)
            | TFun (tsO, oO), TFun (tsN, oN) ->
                isJointType (oO, oN) && tsO.Length = tsN.Length && List.forall isJointType (List.zip tsO tsN)
            | _ -> tO = tN
        /// true iff we generate a lemma for method p
        and generateLemmaFor (p: Path) : bool =
            config.alwaysGenerateLemmas || changedDecls.Contains(p)
        /// true iff we generate an axiom for method p
        and generateAxiomFor (p: Path) : bool =
            (not config.alwaysGenerateLemmas) && (not (changedDecls.Contains(p)))
            && config.generateAxiomsForUnchanged && (not (isJoint p)) && calledByChangedDecls.Contains(p)
        /// true iff we generate a lemma or axiom for method p
        and generateLemmaOrAxiomFor (p: Path) : bool =
            config.alwaysGenerateLemmas || changedDecls.Contains(p)
            || (config.generateAxiomsForUnchanged && (not (isJoint p)) && calledByChangedDecls.Contains(p))
        /// true iff e is a method and we generate a lemma or axiom for e
        and generateLemmaOrAxiomForExpr (e: Expr) : bool =
            match e with
            | EMemberRef (_, m, _) -> generateLemmaOrAxiomFor m
            | _ -> false
        /// true iff e is a method call such that we generate an axiom for the method and we generate an axiom
        /// for each argument we generate a lemma or axiom in the method call
        and generateAxiomForMethodApply (e: Expr) : bool =
            match e with
            | EMethodApply (receiver, method, tpargs, exprs, ghost) ->
                generateAxiomFor method &&
                exprs |> List.forall (fun expr ->
                    match expr with
                    | EMemberRef (_, m, _) ->
                        if generateLemmaOrAxiomFor m then
                            generateAxiomFor m
                        else
                            true
                    | _ -> true )
            | _ -> false
        /// a helper method for specialized lemma names
        and nameForEMemberRef (e: Expr) : string =
            match e with
            | EMemberRef (_, m, _) -> m.ToString().Replace('.', '_')
            | _ -> failwith "nameForEMemberRef called without an EMemberRef"
        /// get the specialized lemma name for an invocation
        and getSpecializedLemmaName (e: Expr) : string =
            match e with
            | EMethodApply (receiver, method, tpargs, exprs, ghost) ->
                method.name + "_" + (
                exprs |> List.indexed |> List.filter (fun x -> generateLemmaOrAxiomForExpr (snd x))
                |> List.map (fun (i, x) -> i.ToString() + "_" + nameForEMemberRef x)
                |> String.concat "_" ) + "_bc"
            | _ -> failwith "getSpecializedLemmaName called without an EMethodApply"
        and getSpecializedArgumentLocations (e: Expr) : int list =
            match e with
            | EMethodApply (receiver, method, tpargs, exprs, ghost) ->
                exprs |> List.indexed |> List.filter (fun x -> generateLemmaOrAxiomForExpr (snd x)) |> List.map fst
            | _ -> failwith "getSpecializedArgumentLocations called without an EMethodApply"
        /// names for a name s: OLD, NEW, (forward translation function, backward translation function)
        and name (s: string) =
            s + "_O", s + "_N", (s + "_forward", s + "_backward")
        /// like name, but also accounts for name changes
        and name2 (s: string, t: string) =
            s + "_O",
            t + "_N",
            if s = t then
                (s + "_forward", s + "_backward")
            else
                (s + "_to_" + t, t + "_back_to_" + s) // TODO make names more uniform
        /// for a type argument: a ---> a_O, a_N, a_forward: a_O -> a_N, a_backward: a_N -> a_O (variance is kept)
        and typearg (a: TypeArg) : TypeArg * TypeArg * (LocalDecl * LocalDecl) =
            let v = snd a
            let aO, aN, aT = name (fst a)
            (aO, v),
            (aN, v),
            (LocalDecl(fst aT, TFun([ TVar aO ], TVar aN), false), LocalDecl(snd aT, TFun([ TVar aN ], TVar aO), false))
        /// like typearg, but also accounts for type argument name changes
        and typearg2 (a: TypeArg, b: TypeArg) : TypeArg * TypeArg * (LocalDecl * LocalDecl) =
            if a = b then
                typearg a
            else
                let nameO, nameN, nameT = name2 (fst a, fst b)
                (nameO, snd a),
                (nameN, snd b),
                (LocalDecl(fst nameT, TFun([ TVar nameO ], TVar nameN), false),
                 LocalDecl(snd nameT, TFun([ TVar nameN ], TVar nameO), false))
        /// heuristically picks a variable name for a type name
        and varname (n: string) = n.Chars(0).ToString()
        /// Remove Joint/Old/New prefixes from paths
        and RemovePrefix =
            { new Traverser.Identity() with
                override this.path(ctx: Context, p: Path) =
                    p.unprefix() }
        /// translates every name (path or type/term variable) to either its OLD or NEW name
        /// a -> a_O or a_N
        /// optional argument ldmap:
        /// for each localdecl in the map, translate it to the expr; keep other localdecls untranslated
        and NameTranslator (old: bool, ldmap: Map<LocalDecl, Expr>) =
            { new Traverser.Identity() with
                override this.path(ctx: Context, p: Path) =
                    let pO, pN, _ = path p
                    if old then pO else pN

                override this.expr(ctx: Context, e: Expr) =
                    match e with
                    | EVar n ->
                        let ld = ctx.lookupLocalDeclO(n)
                        if ld.IsSome then
                            if ldmap.ContainsKey(ld.Value) then
                                this.expr(ctx, ldmap[ld.Value]) // translate to old/new
                            else
                                e // locally bound variables are not translated
                        else
                            let nO, nN, _ = name n
                            EVar(if old then nO else nN)
                    | EThis ->
                        if ctx.thisDecl.IsSome then
                            EVar(ctx.thisDecl.Value.name)
                        else
                            EThis
                    | _ -> this.exprDefault (ctx, e)

                override this.tp(ctx: Context, t: Type) =
                    match t with
                    | TVar n ->
                        let nO, nN, _ = typearg (plainTypeArg n)
                        TVar(if old then fst nO else fst nN)
                    | _ -> this.tpDefault (ctx, t) }
        /// translate non-local variables a -> a_N
        /// translate local variables (a:A) -> A_forward(a)
        and ForwardLocalDeclTranslator (lds: LocalDecl list) =
            { new Traverser.Identity() with
                override this.path(ctx: Context, p: Path) =
                    let _, pN, _ = path p
                    pN

                override this.expr(ctx: Context, e: Expr) =
                    match e with
                    | EVar n ->
                        if ctx.lookupLocalDeclO(n).IsSome then
                            e // locally bound variables in the new context are not translated
                        elif List.exists (fun (x: LocalDecl) -> x.name = n) lds then
                            // generate forward translation
                            let ld =
                                List.findBack (fun (x: LocalDecl) -> x.name = n) lds
                            // When called from insertAssertionsAtResults, some types may have redundant prefixes.
                            // We have to remove them before calling tp()
                            let ldtp = RemovePrefix.tp(ctx, ld.tp)

                            let _, _, (tT1, _) = tp (ldtp, ldtp)
                            tT1 e
                        else
                            let _, nN, _ = name n
                            EVar(nN)
                    | EThis ->
                        if ctx.thisDecl.IsSome then
                            EVar(ctx.thisDecl.Value.name)
                        else
                            EThis
                    | EConstructorApply (cons, tpargs, args) ->
                        let datatypeDecl = ctx.lookupByPath (cons.parent)

                        match datatypeDecl with
                        | Datatype (name, tpvars, datatypeConstructors, members, meta) ->
                            let constructorDecl =
                                List.find (fun (c: DatatypeConstructor) -> c.name = cons.name) datatypeConstructors

                            if constructorDecl.ins.Length <> args.Length then
                                failwith "datatype constructor called with different number of arguments"
                            else
                                this.exprDefault (ctx, e)
                        | _ -> failwith "EConstructorApply called without a datatype"
                    | EMethodApply (receiver, method, tpargs, exprs, ghost) ->
                        let methodDecl = ctx.lookupByPath (method)

                        match methodDecl with
                        | Method (_, _, _, inputSpec, _, _, _, _, _, _, _, _, _) ->
                            if inputSpec.decls.Length <> exprs.Length then
                                failwith "method called with different number of arguments"
                            else
                                this.exprDefault (ctx, e)
                        | _ -> failwith "EMethodApply called without a method"
                    | _ -> this.exprDefault (ctx, e)

                override this.tp(ctx: Context, t: Type) =
                    match t with
                    | TVar n ->
                        let _, nN, _ = typearg (plainTypeArg n)
                        TVar(fst nN)
                    | _ -> this.tpDefault (ctx, t) }
        /// for each method call, if there is a corresponding backward compatibility lemma, invoke it
        /// while translating variables to old names
        /// e.g., foo(x) ----> (foo_bc(x_O); Old.foo(x_O))
        /// for each reveal statement, reveal both the old and the new ones
        /// e.g., reveal foo(); ---> {reveal Old.foo(); reveal New.foo();}
        and PrependLemmaCalls (oldCtx: Context, newCtx: Context, ldmap: Map<LocalDecl, Expr>) =
            { new Traverser.Identity() with
                override this.path(ctx: Context, p: Path) =
                    let pO, _, _ = path p
                    pO

                override this.expr(ctx: Context, e: Expr) =
                    let eDefault = this.exprDefault (ctx, e)

                    match e with
                    | EVar n ->
                        let ld = ctx.lookupLocalDeclO(n)
                        if ld.IsSome then
                            if ldmap.ContainsKey(ld.Value) then
                                this.expr(ctx, ldmap[ld.Value]) // translate to old
                            else
                                e // locally bound variables are not translated
                        else
                            let nO, nN, _ = name n
                            EVar(nO)
                    | EAnonApply (EVar n, args) ->
                        let ld = ctx.lookupLocalDeclO(n)
                        if ld.IsSome then
                            if ldmap.ContainsKey(ld.Value) then
                                match ldmap[ld.Value] with
                                | EMemberRef(receiver, mmbr, tpargs) ->
                                    // replace with EMethodApply to be able to append lemma calls here
                                    this.expr(ctx, EMethodApply (receiver, mmbr, tpargs, args, false))
                                | _ -> eDefault
                            else
                                eDefault
                        else
                            eDefault
                    | EThis ->
                        if ctx.thisDecl.IsSome then
                            EVar(ctx.thisDecl.Value.name)
                        else
                            EThis
                    | EMethodApply (receiver, method, tpargs, exprs, ghost) ->
                        let methodDeclO = ctx.lookupByPathOption (method)
                        let methodDeclN = newCtx.lookupByPathOption (method)

                        if generateLemmaOrAxiomFor method
                           && methodDeclO.IsSome
                           && methodDeclN.IsSome then
                            match methodDeclO.Value, methodDeclN.Value with
                            | Method(methodType = IsLemma), _
                            | Method(methodType = IsMethod), _ -> eDefault
                            | Method (_, _, _, insO, _, _, _, _, _, _, isStatic, _, _),
                              Method (_, _, _, insN, _, _, _, _, _, _, _, _, _) when
                                insO.decls.Length = insN.decls.Length ->
                                try
                                    // Equivalent to (if we have not generated specializedLemmas before)
                                    // let specializedLemma = config.specializeHigherOrderLemmas &&
                                    //                        List.exists generateLemmaOrAxiomForExpr exprs
                                    let specializedLemma = config.specializeHigherOrderLemmas && (
                                        Map.tryFind method specializedLemmas |> Option.exists (List.contains e))
                                    
                                    // Prepend a lemma call to this method application.
                                    // Only prepend the lemma call if the old method and the new method have the same
                                    // number of inputs.
                                    // See also the translation for Diff.Method below in declSameOrUpdate.
                                    let parentDeclO = ctx.lookupByPath (method.parent)
                                    // Do not set thisDecl again because "this" is the current method
                                    // instead of the method being called.
                                    // Do not use exprOld and exprNew because they add the old/new suffix again.

                                    let newLocalDecls =
                                        List.filter (fun ld -> not (List.contains ld oldCtx.vars)) ctx.vars

                                    let oldNameCtx = ctx

                                    let instanceInputs =
                                        if isStatic then
                                            []
                                        else
                                            match receiver with
                                            | StaticReceiver _ -> failwith "unexpected static receiver"
                                            | ObjectReceiver (r, _) ->
                                                [ NameTranslator(true, Map.empty).expr (oldNameCtx, r)
                                                  ForwardLocalDeclTranslator(newLocalDecls)
                                                      .expr (newCtx, r) ]

                                    let instanceTypeArgs =
                                        match receiver with
                                        | StaticReceiver ct -> ct.tpargs
                                        | ObjectReceiver (_, tp) ->
                                            match tp with
                                            | TApply (_, args) -> args
                                            | _ -> []

                                    let instanceTypeArgTranslationInputs =
                                        instanceTypeArgs
                                        |> List.collect
                                            (fun (t: Type) ->
                                                let _, _, (tT1, tT2) = tpAbstracted ("x", t, t)

                                                if config.generateBackwardTranslationFunctions then
                                                    [ tT1; tT2 ]
                                                else
                                                    [ tT1 ])

                                    // the type arguments (of type Type, not TypeArg)
                                    let tsO, tsN = tpargs, tpargs

                                    let tsT =
                                        List.collect
                                            (fun (t: Type) ->
                                                let _, _, (tForward, tBackward) = tpAbstracted ("x", t, t)

                                                if config.generateBackwardTranslationFunctions then
                                                    [ tForward; tBackward ]
                                                else
                                                    [ tForward ])
                                            tpargs

                                    let typeParams = Utils.listInterleave (tsO, tsN)

                                    // the old inputs and new inputs
                                    let insO = exprs |>
                                               (if specializedLemma then
                                                         List.filter (generateLemmaOrAxiomForExpr >> not)
                                                         else id) |>
                                               List.map (fun e -> NameTranslator(true, Map.empty).expr (oldNameCtx, e))

                                    let insN = exprs |>
                                               (if specializedLemma then
                                                         List.filter (generateLemmaOrAxiomForExpr >> not)
                                                         else id) |>
                                               List.map (fun e ->
                                                   ForwardLocalDeclTranslator(newLocalDecls).expr (newCtx, e))

                                    let inputs =
                                        instanceInputs
                                        @ instanceTypeArgTranslationInputs
                                          @ tsT @ insO @ insN

                                    let lemmaReceiver, lemmaName =
                                        match parentDeclO with
                                        | Datatype _ ->
                                            let ct =
                                                { path = method.parent.parent
                                                  tpargs = [] }

                                            StaticReceiver(ct),
                                            method.parent.parent.child (method.parent.name + "_" + method.name + "_bc")
                                        | Module _ ->
                                            if specializedLemma then
                                                receiver, method.parent.child (getSpecializedLemmaName e)
                                            else
                                                receiver, method.parent.child (method.name + "_bc")
                                        | _ -> failwith (unsupported $"parent declaration {parentDeclO}")

                                    let lemmaCall =
                                        EMethodApply(lemmaReceiver, lemmaName, typeParams, inputs, true)

                                    EBlock [ lemmaCall; eDefault ]
                                with _ -> eDefault // fall back to default if there is anything wrong prepending the lemma
                            | Method _, Method _ -> eDefault
                            | _ -> eDefault // failwith "EMethodApply called without a method"
                        else
                            eDefault
                    | EReveal exprs ->
                        // duplicate the reveal statement with new context
                        let newReveal = EReveal (List.map (fun e -> NameTranslator(false, Map.empty).expr (ctx, e)) exprs)
                        EBlock [ eDefault ; newReveal ]
                    | _ -> eDefault

                override this.tp(ctx: Context, t: Type) =
                    match t with
                    | TVar n ->
                        let nO, _, _ = typearg (plainTypeArg n)
                        TVar(fst nO)
                    | _ -> this.tpDefault (ctx, t) }
        /// After PrependLemmaCalls, keep only the lemma calls
        /// e.g., (foo_bc(x_O); Old.foo(x_O)) ----> foo_bc(x_O);
        and KeepOnlyLemmaCalls =
            { new Traverser.Identity() with
                override this.case(ctx, case) =
                    let ctxE = ctx.add case.vars
                    let bodyT = this.expr (ctxE, case.body)

                    { vars = case.vars
                      patterns = case.patterns
                      body = bodyT }

                override this.expr(ctx: Context, e: Expr) =
                    let rcE (e: Expr) = this.expr (ctx, e)

                    let rcEo (eO: Expr option) = Option.map rcE eO

                    let rcEol (e: Expr option) =
                        match e with
                        | Some expr -> [ this.expr (ctx, expr) ]
                        | None -> []

                    let rcR (rcv: Receiver) =
                        match rcv with
                        | StaticReceiver ct -> EBlock []
                        | ObjectReceiver (e, tp) -> this.expr (ctx, e)

                    let removeEmptyBlock =
                        List.filter
                            (fun b ->
                                match b with
                                | EBlock exprs -> exprs.Length > 0
                                | _ -> true)

                    let block (es: Expr list) = EBlock(removeEmptyBlock es)
                    let rcEs (es: Expr list) = block (List.map rcE es)

                    match e with
                    | EBlock exprs ->
                        if exprs.Length = 2 then // a potential lemma call
                            match exprs.Head with
                            | EMethodApply (lemmaReceiver, lemmaName, typeParams, inputs, true) when
                                lemmaName.name.EndsWith("_bc") ->
                                EBlock(
                                    exprs.Head
                                    :: removeEmptyBlock (this.exprList (ctx, exprs.Tail))
                                )
                            | _ -> block (this.exprList (ctx, exprs))
                        else
                            rcEs exprs
                    | ENew (ct, args) -> rcEs args
                    | EMemberRef (r, m, ts) -> rcR r
                    | EMethodApply (r, m, ts, es, isG) -> block (rcR r :: List.map rcE es)
                    | EConstructorApply (c, ts, es) -> rcEs es
                    | EQuant (q, lds, r, ens, b) ->
                        let ctxE = ctx.add lds
                        let bT = this.expr (ctxE, b)
                        EQuant(q, lds, r, [], bT)
                    | EOld e -> block [ rcE e ]
                    | ETuple es -> rcEs es
                    | EProj (e, i) -> block [ rcE e ]
                    | ESet (t, es) -> rcEs es
                    | ESetComp (lds, p, b) ->
                        let ctxE = ctx.add lds
                        let bT = this.expr (ctxE, b)
                        ESetComp(lds, p, bT)
                    | ESeq (t, es) -> rcEs es
                    | ESeqConstr (t, l, i) -> block [ rcE l; rcE i ]
                    | ESeqSelect (s, t, elem, frI, toI) -> block ([ rcE s ] @ rcEol frI @ rcEol toI)
                    | ESeqUpdate (s, i, e) -> block [ rcE s; rcE i; rcE e ]
                    | EToString es -> rcEs es
                    | EArray (t, dim, init) ->
                        let initT =
                            match init with
                            | Uninitialized -> []
                            | ValueList es -> List.map rcE es
                            | ComprehensionLambda e -> [ rcE e ]

                        block initT
                    | EMultiSelect (a, i) -> block [ rcE a ]
                    | EArrayUpdate (a, i, e) -> block [ rcE a; rcE e ]
                    | EMapKeys m -> block [ rcE m ]
                    | EMapValues m -> block [ rcE m ]
                    | EMapDisplay kvs ->
                        (List.fold (fun l (eKey, eVal) -> rcE eVal :: rcE eKey :: l) [] kvs)
                        |> List.rev
                        |> block
                    | EMapComp (lds, p, tL, tR) ->
                        Console.WriteLine("WARNING: dropping EMapComp in KeepOnlyLemmaCalls")
                        EBlock []
                    | EFun (ins, cond, out, bd) -> EFun(ins, cond, out, this.expr (ctx.add ins, bd))
                    | EAnonApply (f, es) -> block (rcE f :: List.map rcE es)
                    | EUnOpApply (op, e) -> block [ rcE e ]
                    | EBinOpApply (op, e1, e2) -> block [ rcE e1; rcE e2 ]
                    | ELet (v, x, o, lhs, df, bd) ->
                        let ctxI = ctx.add (v)
                        ELet(v, x, o, lhs, df, this.expr (ctxI, bd))
                    | ETypeConversion (e, t) -> block [ rcE e ]
                    | ETypeTest (e, t) -> block [ rcE e ]
                    | EIf (c, t, e) -> EIf(c, rcE t, rcEo e)
                    | EAlternative (conds, bodies) -> EAlternative(conds, List.map rcE bodies)
                    | EFor (index, init, ls, up, body) ->
                        let innerCtx = ctx.add [ index ]
                        let bodyT = this.expr (innerCtx, body)
                        EFor(index, init, ls, up, bodyT)
                    | EWhile (c, e, l) -> EWhile(c, rcE e, l)
                    | EReturn es -> rcEs es
                    | EMatch (e, t, cases, d) ->
                        let csT =
                            List.map (fun (c: Case) -> this.case (ctx, c)) cases

                        let dfltT = this.exprO (ctx, d)
                        EMatch(e, t, csT, dfltT)
                    | EDecls (vars, lhs, rhs) -> EDecls(vars, lhs, List.map (fun u -> this.updateRHS (ctx, u)) rhs)
                    | EUpdate (es, rhs) -> EUpdate(es, this.updateRHS (ctx, rhs))
                    | EPrint es -> rcEs es
                    | EAssert (e, p, l) -> block (rcE e :: rcEol p)
                    | EAssume e -> block [ rcE e ]
                    | EReveal es -> rcEs es
                    | EExpect e -> block [ rcE e ]
                    | ECommented (s, e) -> block [ rcE e ]
                    | EVar _
                    | EThis
                    | EReal _
                    | EInt _
                    | EBool _
                    | EChar _
                    | EString _
                    | EBreak _
                    | ENull _
                    | EUnimplemented -> EBlock [] }
        /// Insert assertions at the results of the old expression that the forward translation of the old result
        /// is equal to the new result.
        /// e.g.,
        /// e ----> assert resultN == forward(e);
        /// 
        /// if cond then e1 else e2
        /// ---->
        /// if (cond) { assert resultN == forward(e1); } else { assert resultN == forward(e2); }
        ///
        /// match e {
        ///   case c1 => e1
        ///   case c2 => e2
        /// }
        /// ---->
        /// match e {
        ///   case c1 => assert resultN == forward(e1);
        ///   case c2 => assert resultN == forward(e2);
        /// }
        ///
        /// var x := / :| df; body
        /// ---->
        /// var x := / :| df; assert resultN == forward(body);
        /// (do not expand let-or-fail statement, i.e., (var x :- df; body))
        ///
        /// forall x :: cond ==> body
        /// ---->
        /// if (forall x :: cond ==> body) {
        ///   forall x | cond
        ///     ensures resultN {
        ///       KeepOnlyLemmaCalls(body)
        ///   }
        /// } else {
        ///   var x :| cond && !body;
        ///   assert !resultN by {
        ///     KeepOnlyLemmaCalls(body)
        ///   }
        /// }
        ///
        /// exists x :: cond && body
        /// ---->
        /// if (exists x :: cond && body) {
        ///   var x :| cond && body;
        ///   assert resultN by {
        ///     KeepOnlyLemmaCalls(body)
        ///   }
        /// } else {
        ///   forall x | cond
        ///     ensures !resultN {
        ///       KeepOnlyLemmaCalls(body)
        ///   }
        /// }
        ///
        /// x => body(x)
        /// ----> (only when config.useForallInFunctionEnsures is also true)
        /// forall x
        ///   ensures resultN(x) == body(x)
        ///   {}
        and insertAssertionsAtResults
            (
                resultO: Expr,
                resultN: Expr,
                resultOTranslation: Expr -> Expr,
                ctx: Context,
                e: Expr,
                ctxN: Context,
                eN: Expr option
            ) =
            let rcE (resultN: Expr) (e: Expr) (eN: Expr option) (ld: LocalDecl list) =
                insertAssertionsAtResults (resultO, resultN, resultOTranslation, ctx.add (ld), e, ctxN.add (ld), eN)

            let rcEb (e: Expr) (eN: Expr option) = EBlock [ rcE resultN e eN [] ]

            let rcEbo (eO: Expr option) (eN: Expr option) =
                match eO with
                | Some e -> Some(rcEb e eN)
                | None -> None

            let eDefault =
                EAssert(EEqual(resultN, reduce (resultOTranslation e)), None, None)

            match e with
            | EIf (c, t, e) ->
                match eN with
                | Some (EIf (cN, tN, eN)) -> EIf(c, rcEb t (Some tN), rcEbo e eN)
                | _ -> // mismatch in new implementation, ignore new implementation
                    EIf(c, rcEb t None, rcEbo e None)
            | EBlock exprs when exprs.Length > 0 ->
                EBlock (exprs[..exprs.Length - 2] @ [ rcE resultN exprs[exprs.Length - 1] (
                    match eN with
                    | Some (EBlock esN) when esN.Length > 0 ->
                        Some esN[esN.Length - 1]
                    | _ -> None) [] ])
            | EMatch (e, t, cases, d) ->
                let rcCase (case: Case) (caseN: Case option) =
                    let bodyT =
                        rcE resultN case.body (Option.map (fun c -> c.body) caseN) case.vars

                    { vars = case.vars
                      patterns = case.patterns
                      body = bodyT }

                let csT =
                    match eN with
                    | Some (EMatch (_, _, casesN, _)) when casesN.Length = cases.Length ->
                        List.map (fun (c: Case, cN: Case) -> rcCase c (Some cN)) (List.zip cases casesN)
                    | _ -> List.map (fun (c: Case) -> rcCase c None) cases

                let dfltT =
                    match d with
                    | None -> None
                    | Some dO ->
                        match eN with
                        | Some (EMatch (_, _, _, dN)) -> Some(rcE resultN dO dN [])
                        | _ -> Some(rcE resultN dO None [])

                EMatch(e, t, csT, dfltT)
            | ELet (v, x, o, lhs, df, bd) when not o ->
                let bdT =
                    match eN with
                    | Some (ELet (_, xN, oN, _, _, bdN)) when xN = x && oN = o -> rcE resultN bd (Some bdN) v
                    | _ -> rcE resultN bd None v

                ELet(v, x, o, lhs, df, bdT)
            | EQuant (quant, ld, cond, ens, body) ->
                let nonDeterministicVars = List.map localDeclTerm ld

                let letCondNot =
                    match cond with
                    | Some c -> EBinOpApply("And", c, notExpr body)
                    | _ -> notExpr body

                let letCond =
                    match cond with
                    | Some c -> EBinOpApply("And", c, body)
                    | _ -> body

                let eBody =
                    YIL.block (KeepOnlyLemmaCalls.expr (ctx, body))

                let newEnsures =
                    match eN with
                    | Some (EQuant (quantN, _, _, _, bodyN)) when quantN = quant ->
                        // match (ignoring condition), ensures the new body is true; label=None
                        // Do not use exprNew because it adds the new suffix but we want forward translation
                        [ ForwardLocalDeclTranslator(ld).expr (ctxN, bodyN), None ]
                    | _ -> []

                let newEnsuresNot =
                    match eN with
                    | Some (EQuant (quantN, _, _, _, bodyN)) when quantN = quant ->
                        // match (ignoring condition), ensures the new body is false; label=None
                        // Do not use exprNew because it adds the new suffix but we want forward translation
                        [ notExpr (ForwardLocalDeclTranslator(ld).expr (ctxN, bodyN)), None ]
                    | _ -> []

                let newAssert =
                    match eN with
                    | Some (EQuant (quantN, _, _, _, bodyN)) when quantN = quant ->
                        // match (ignoring condition), assert the new body is true; label=None
                        // Do not use exprNew because it adds the new suffix but we want forward translation
                        EAssert(ForwardLocalDeclTranslator(ld).expr (ctxN, bodyN), Some eBody, None)
                    | _ -> eBody

                let newAssertNot =
                    match eN with
                    | Some (EQuant (quantN, _, _, _, bodyN)) when quantN = quant ->
                        // match (ignoring condition), assert the new body is false; label=None
                        // Do not use exprNew because it adds the new suffix but we want forward translation
                        Some(
                            EAssert(
                                notExpr (ForwardLocalDeclTranslator(ld).expr (ctxN, bodyN)),
                                Some eBody,
                                None
                            )
                        )
                    | _ -> None

                if quant = Quantifier.Forall then
                    let quantExpr =
                        EQuant(quant, ld, cond, ens @ newEnsures, eBody)

                    let letExpr =
                        Option.map
                            (fun e -> EBlock [ ELet(ld, false, false, nonDeterministicVars, [ letCondNot ], e) ])
                            newAssertNot

                    EIf(e, EBlock [ quantExpr ], letExpr)
                else
                    let letExpr =
                        EBlock [ ELet(ld, false, false, nonDeterministicVars, [ letCond ], newAssert) ]

                    let quantExpr =
                        EBlock [ EQuant(Quantifier.Forall, ld, cond, newEnsuresNot, eBody) ]

                    EIf(e, letExpr, Some quantExpr)
            | EBinOpApply (op, arg1, arg2) when op = "NeqCommon" || op = "EqCommon" ->
                // (arg1 == EQuant), (arg1 != EQuant)
                // generate the following:
                // if (arg1) {
                //   ... (generate proof sketch for EQuant)
                // } else {
                //   ... (generate proof sketch for EQuant)
                // }
                let eNarg2 =
                    match eN with
                    | Some (EBinOpApply (_, _, arg2N)) ->
                        Some arg2N
                    | _ -> None
                let arg1, arg2 =  // "==" and "!=" are symmetric
                    match arg1 with
                    | EQuant _ -> arg2, arg1
                    | _ -> arg1, arg2
                match arg2 with
                | EQuant (quant, ld, cond, ens, body) ->
                    let eNtrueBranch =
                        match eNarg2 with
                        | Some (EQuant _) -> eNarg2
                        | _ -> None
                    let trueBranch = EBlock [rcE resultN arg2 eNtrueBranch []]
                    let eNfalseBranch =
                        match eNarg2 with
                        | Some (EQuant (quantN, ldN, condN, ensN, bodyN)) ->
                            Some (EQuant (quantN.negate(), ldN, condN, ensN, notExpr bodyN))
                        | _ -> None
                    let falseBranch = EBlock [rcE resultN (EQuant (quant.negate(), ld, cond, ens, notExpr body)) eNfalseBranch []]
                    if op = "EqCommon" then
                        EIf (arg1, trueBranch, Some falseBranch)
                    else
                        EIf (arg1, falseBranch, Some trueBranch)
                | _ -> eDefault  // not EQuant, use the default case
            | EFun (vars, cond, out, body) when config.useForallInFunctionEnsures ->
                // return a function, should only be at top level
                let eVars = List.map localDeclTerm vars
                match eN with
                | Some (EFun (_, _, outN, bodyN)) ->
                    let _, _, (outT, _) = tp (out, outN)
                    let outExprN = EAnonApply(resultN, eVars)
                    let outExprO = outT (EAnonApply(resultO, eVars))
                    let resultBody = EBlock [ rcE outExprN body (Some bodyN) vars ]
                    // Note: Dafny is not happy if we dump the proof directly into the ensures clause of the forall
                    // statement. We need to keep the proof in the forall body.
                    EQuant (Quantifier.Forall, vars, Option.map fst cond, [ EEqual (outExprN, outExprO), None ], resultBody)
                | _ -> eDefault // the new implementation is not a direct function
            | _ -> eDefault
        /// input translations for backward compatibility lemmas
        and backward_compatible
            (insT: (Condition * Condition) list)
            (insO: Expr list)
            (insN: Expr list)
            : Condition list =
            let translationCondition (oldToNew: Expr) (newToOld: Expr) (inO: Expr) (inN: Expr) =
                if not config.useForallInFunctionRequires then
                    // x_N == forward(x_O)
                    EEqual(inN, oldToNew)
                else
                    match oldToNew with
                    | EFun (vars, cond, _, body) ->
                        // function f: A -> B
                        // oldToNew is (a_N: A_N) => B_forward(f_O(A_backward(a_N)))
                        // forall a_N: A_N :: f_N(A_N) == B_forward(f_O(A_backward(a_O)))
                        EQuant(
                            Forall,
                            vars,
                            Option.map fst cond,
                            [],
                            EEqual(EAnonApply(inN, List.map localDeclTerm vars), body)
                        )
                    | _ ->
                        // not a function
                        // x_N == forward(x_O)
                        EEqual(inN, oldToNew)

            List.map
                (fun ((f1, f2), inO: Expr, inN: Expr) ->
                    translationCondition (fst f1) (fst f2) inO inN, snd f1)
                (List.zip3 insT insO insN)
        /// lossless condition for translation functions
        and lossless (ctx: Context) (tO: Type) (tT: (Expr -> Expr) * (Expr -> Expr)) : Condition =
            // forall x1_O: U_O :: U_backward(U_forward(x1_O)) == x1_O
            let nO, _, _ = name (ctx.getTempLocalDeclName())
            let ld = LocalDecl(nO, tO, true)
            EQuant(Forall, [ ld ], None, [], EEqual((snd tT) ((fst tT) (EVar nO)), EVar nO)), None
        /// output translation for backward compatibility lemmas
        and backward_compatible_ensures
            (outputTypeT: ((Expr -> Expr) * (Expr -> Expr)) option)
            (outputTypeN: Type option)
            (canTranslateOutput: bool)
            (resultO: Expr)
            (resultN: Expr)
            : Condition =
            match outputTypeT, outputTypeN, canTranslateOutput with
            | Some otT, Some otN, true ->
                let resultOTranslated = reduce ((fst otT) resultO)
                if not config.useForallInFunctionEnsures then
                    EEqual(resultN, resultOTranslated), None
                else
                    match otN with
                    | TFun (ts_n, u_n) ->
                        // x1:t1, ..., xn:tn
                        let lds_n =
                            List.indexed ts_n
                            |> List.map (fun (i, t) -> LocalDecl("x" + (i + 1).ToString(), t, false))
                        // f is the return value of the function 
                        // function f: (t1, ..., tn) -> u
                        // forall x1:t1, ..., xn:tn :: New.f(x1, ..., xn) == f_forward(Old.f)(x1, ..., xn)
                        EQuant(
                            Forall,
                            lds_n,
                            None,
                            [],
                            EEqual(EAnonApply(resultN, List.map localDeclTerm lds_n),
                                   EAnonApply(resultOTranslated, List.map localDeclTerm lds_n))
                        ), None
                    | _ -> EEqual(resultN, resultOTranslated), None
            | None, None, true -> EBool true, None
            | _ -> ECommented("cannot translate output type", EBool false), None
        /// generate proof for backward compatibility theorem
        and proof
            (oldCtx: Context)
            (newCtx: Context)
            (ldmap: Map<LocalDecl, Expr>)
            (e: Expr)
            (resultO: Expr)
            (resultN: Expr)
            (resultOTranslation: Expr -> Expr)
            (generateRevealO: bool)
            (generateRevealN: bool)
            : Expr option =
            let oldCtxWithSuffix =
                oldCtx.translateLocalDeclNames
                    (fun (n: LocalDecl) ->
                        if ldmap.ContainsKey(n) then
                            n.name
                        else
                            let nO, _, _ = name n.name
                            nO)

            let newCtxWithSuffix =
                newCtx.translateLocalDeclNames
                    (fun (n: LocalDecl) ->
                        if ldmap.ContainsKey(n) then
                            n.name
                        else
                            let _, nN, _ = name n.name
                            nN)

            // e is the old implementation, e.g.,
            // foo(x)
            let eO =
                if config.generateLemmaCalls then
                    PrependLemmaCalls(oldCtxWithSuffix, newCtxWithSuffix, ldmap)
                        .expr (oldCtxWithSuffix, e)
                else
                    exprOld oldCtx ldmap e
            // eO is the old implementation with lemma calls and translated names, e.g.,
            // (foo_bc(x_O); Old.foo(x_O))
            let eAssertion =
                if config.expandAssertions then
                    insertAssertionsAtResults (resultO, resultN, resultOTranslation, oldCtx, eO, newCtxWithSuffix, Some e)
                else
                    EAssert(EEqual(resultN, reduce (resultOTranslation eO)), None, None)
            // eAssertion is the proof sketch, e.g.,
            // { foo_bc(x_O); assert resultN == forward(Old.foo(x_O)); }
            let resultToReveal generateReveal result =
                if generateReveal then
                    match result with
                    | EMethodApply (receiver, method, tpargs, exprs, ghost) ->
                        [ EReveal([ EMethodApply(receiver, method, tpargs, [], ghost) ]) ]
                    | _ -> failwith "Proofs should only generated for method applications"
                else
                    []
            // resultToReveal is a function to generate the reveal statements for the original methods.
            // These reveal statements should be prepended to the proof sketch if the original method is opaque. 
            if config.generateProof then
                Some(
                    EBlock(
                        resultToReveal generateRevealO resultO
                        @ resultToReveal generateRevealN resultN
                          @ YIL.exprToList eAssertion
                    )
                )
            else
                Some(EBlock [])
        /// extends declaration-translation to lists 
        and decls (contextO: Context) (contextN: Context) (dsD: Diff.List<Decl, Diff.Decl>) =
            List.collect (decl contextO contextN) dsD.elements
        /// entry point for declaration-translation
        and decl (contextO: Context) (contextN: Context) (dD: Diff.Elem<Decl, Diff.Decl>) : Decl list =
            match dD with
            | Diff.Same d -> declSameOrUpdate contextO contextN (d, d) (Diff.idDecl d)
            | Diff.Add _
            | Diff.Delete _ -> [] // nothing to generate for added/deleted declarations
            | Diff.Update (d, n, df) -> declSameOrUpdate contextO contextN (d, n) df
        /// core function for declaration-translation
        and declSameOrUpdate(contextO: Context)(contextN: Context)(declO: Decl, declN: Decl)(dif: Diff.Decl): Decl list =
            let n =
                match dif.name with
                | Diff.SameName n -> n
                | Diff.Rename _ -> failwith (unsupported "renamed declaration")

            let p = contextO.currentDecl.child (n)
            let pO, pN, pT = path p

            match dif with
            | Diff.Class (_, _, _, msD) ->
                // TODO: functional instead of relational approach here
                // TODO: for now, do not generate any translation for constituent parts of a class, as it is
                // syntactically broken
                // let tvs = declO.tpvars
                // let typeParams, inSpec, outSpec, xtO, xtN = typeDeclHeaderMain (p, n, tvs)
                // let xO, xN = localDeclTerm xtO, localDeclTerm xtN
                // We use the strictest possible relation here: only identical objects are related.
                // That is very simple and sufficient for now.
                // A more general treatment might use some kind of observational equality, possibly using coalgebraic methods.
                // let body = EEqual(xO,xN)
                // let relation = Method(NonStaticMethod IsFunction, pT.name, typeParams, inSpec, outSpec, Some body, false, true, emptyMeta)
                // belongs to the implementation part.
                // let memberLemmas = decls ctxI msD
                // wrap all declarations generated by members into a module to get the right paths
                // let decls = [ relation; Module(n, memberLemmas, emptyMeta) ]
                []
            | Diff.ClassConstructor _ ->
                // Depending on how we treat classes, we could generate a lemma here.
                // With the current minimal treatment of classes, nothing is needed.
                []
            | Diff.Import _ -> [ declO ] // Preserve all import statements
            | Diff.Export _ -> [] // Remove all export statements
            | Diff.DUnimplemented -> [ declO ]
            | Diff.Module (name, msD) ->
                let imports =
                    List.choose
                        (function
                        | Import it -> Some it
                        | _ -> None)

                let ctxOm =
                    List.fold
                        (fun (ctx: Context) -> ctx.addImport)
                        (contextO.enter(name.getOld).clearImport ())
                        (imports (msD.getOld ()))

                let ctxNm =
                    List.fold
                        (fun (ctx: Context) -> ctx.addImport)
                        (contextN.enter(name.getNew).clearImport ())
                        (imports (msD.getNew ()))

                [ Module(n, decls ctxOm ctxNm msD, contextO.currentMeta ()) ]
            | Diff.TypeDef (_, tvsD, superD, exprD) ->
                match declO with
                | TypeDef (_, tvs_o, super, _, isNew, _) ->
                    // TypeDefs produce methods
                    let (typeParams: TypeArg list), inSpec, outSpec, xtO, xtN, inSpecBack, outSpecBack =
                        typeDeclHeader (p, declO, declN)

                    let xO = localDeclTerm xtO
                    let xN = localDeclTerm xtN

                    let body =
                        if isJoint p && typeParams.IsEmpty then
                            // for joint typedefs without typeargs, generate identity function
                            xO
                        elif isNew then
                            // new types are new primitive types, so return identity map
                            // but we may need explicit type conversion
                            ETypeConversion(xO, xtN.tp)
                        else
                            match declN with
                            | TypeDef (_, tvs_n, superN, _, _, _) ->
                                let bd =
                                    // try to generate a call to the translation function of the super datatype first
                                    match super, superN with
                                    | TApply (opO, argsO), TApply (opN, argsN) ->
                                        let dtO = contextO.lookupByPath opO
                                        let dtN = contextN.lookupByPath opN
                                        let dtDo = Differ.decl (dtO, dtN)
                                        match dtDo with
                                        | Some (Diff.Datatype _) ->
                                            let _, _, names = name2 (dtO.name, dtN.name)
                                            let ct = { path = opO.parent; tpargs = [] }
                                            let instantiatedTypeT = List.map tp (List.zip argsO argsN)
                                            let tsT =
                                                List.map (fun (o, n, (t1, t2)) -> (abstractRel ("x", o, n, t1), abstractRel ("x", n, o, t2))) instantiatedTypeT
                                            let inputs = (Utils.listInterleave (List.unzip tsT)) @ [ xO ]
                                            Some (EMethodApply (StaticReceiver ct, opO.parent.child(fst names), [],
                                                                inputs, false))
                                        | _ -> None
                                    | _ -> None
                                match bd with
                                | Some b -> b
                                | _ ->
                                    // otherwise, call function of supertype
                                    let _, _, superT = tp (super, superN)
                                    (fst superT) xO
                            | _ -> failwith "impossible" // Diff.TypeDef must go with YIL.TypeDef

                    let body_back =
                        if isJoint p && typeParams.IsEmpty then
                            // for joint typedefs without typeargs, generate identity function
                            xN
                        elif isNew then
                            // new types are new primitive types, so return identity map
                            // but we may need explicit type conversion
                            ETypeConversion(xN, xtO.tp)
                        else
                            match declN with
                            | TypeDef (_, tvs_n, superN, _, _, _) ->
                                let bd =
                                    // try to generate a call to the translation function of the super datatype first
                                    match super, superN with
                                    | TApply (opO, argsO), TApply (opN, argsN) ->
                                        let dtO = contextO.lookupByPath opO
                                        let dtN = contextN.lookupByPath opN
                                        let dtDo = Differ.decl (dtO, dtN)
                                        match dtDo with
                                        | Some (Diff.Datatype _) ->
                                            let _, _, names = name2 (dtO.name, dtN.name)
                                            let ct = { path = opO.parent; tpargs = [] }
                                            let instantiatedTypeT = List.map tp (List.zip argsO argsN)
                                            let tsT =
                                                List.map (fun (o, n, (t1, t2)) -> (abstractRel ("x", o, n, t1), abstractRel ("x", n, o, t2))) instantiatedTypeT
                                            let inputs = (Utils.listInterleave (List.unzip tsT)) @ [ xN ]
                                            Some (EMethodApply (StaticReceiver ct, opO.parent.child(snd names), [],
                                                                inputs, false))
                                        | _ -> None
                                    | _ -> None
                                match bd with
                                | Some b -> b
                                | _ ->
                                    // otherwise, call function of supertype
                                    let _, _, superT = tp (super, superN)
                                    (snd superT) xN
                            | _ -> failwith "impossible" // Diff.TypeDef must go with YIL.TypeDef

                    let _, _, names = name p.name

                    Method(
                        IsFunction,
                        fst names,
                        typeParams,
                        inSpec,
                        outSpec,
                        [],
                        [],
                        [],
                        Some body,
                        false,
                        true,
                        false,
                        contextO.currentMeta ()
                    )
                    :: if config.generateBackwardTranslationFunctions then
                           [ Method(
                                 IsFunction,
                                 snd names,
                                 typeParams,
                                 inSpecBack,
                                 outSpecBack,
                                 [],
                                 [],
                                 [],
                                 Some body_back,
                                 false,
                                 true,
                                 false,
                                 contextO.currentMeta ()
                             ) ]
                       else
                           []
                | _ -> failwith ("impossible") // Diff.TypeDef must go with YIL.TypeDef

            | Diff.Datatype (nameD, tvsD, ctrsD, msD) ->
                // generate translation functions

                let ctxOb =
                    contextO
                        .enter(nameD.getOld)
                        .addTpvars (tvsD.getOld ())

                let ctxNb =
                    contextN
                        .enter(nameD.getNew)
                        .addTpvars (tvsD.getNew ())

                if not tvsD.isSameOrUpdated then
                    failwith (
                        unsupported "addition or deletion in type parameters: "
                        + p.ToString()
                    )

                let tvsO =
                    match declO with
                    | Datatype (_, tpvars, _, _, _) -> tpvars
                    | TypeDef (_, tpvars, _, _, _, _) -> tpvars
                    | _ -> failwith ("impossible") // Diff.Datatype must go with YIL.Datatype or YIL.TypeDef

                let tvsN =
                    match declN with
                    | Datatype (_, tpvars, _, _, _) -> tpvars
                    | TypeDef (_, tpvars, _, _, _, _) -> tpvars
                    | _ -> failwith ("impossible") // Diff.Datatype must go with YIL.Datatype or YIL.TypeDef

                // datatype p.name<u,v> = con1(a,u) | con2(b,v) ---> p.name<u,w> = con1(a,u) | con2(b,w)
                // ---->
                // datatype pO<uO,vO> = con1(aO,uO) | con2(bO,vO)
                // datatype pN<uN,wN> = con1(aN,uN) | con2(bN,wN)
                // function pT<uO,uN,vO,wN>(u:uO->uN, v_to_w:vO->wN, xO:pO<uO,vO>) = match xO
                //   | con1(x1,x2) => con1(a(x1),u(x2))
                //   | con2(x1,x2) => con2(b(x1),v_to_w(x2))
                // and accordingly for the general case.
                let typeParams, inSpec, outSpec, xtO, xtN, inSpecBack, outSpecBack =
                    typeDeclHeaderMain (p, n, tvsO, tvsN)

                let mkCase (isForward: bool) (elem: Diff.Elem<YIL.DatatypeConstructor, Diff.DatatypeConstructor>) =
                    // to share code between the cases, we interpret the change as an update
                    // old and new constructor and the diff
                    let ctrO, ctrN, ctrD =
                        match elem with
                        | Diff.Update (o, n, d) -> o, n, d
                        | _ ->
                            // if not an Update, we use default values that are only used partially below
                            elem.yil, elem.yil, Diff.idConstructor elem.yil

                    let insO, _, _ =
                        List.unzip3 (List.map localDecl ctrO.ins)

                    let _, insN, _ =
                        List.unzip3 (List.map localDecl ctrN.ins)

                    let insT1 =
                        List.map
                            (fun x ->
                                match x with
                                | Some (a, b, (c, d)) -> c
                                | None -> (missingTerm, None))
                            (List.map (Option.map localDecl2) (ctrD.ins().getSameOrUpdateForNew ()))

                    let insT2 =
                        List.map
                            (fun x ->
                                match x with
                                | Some (a, b, (c, d)) -> d
                                | None -> (missingTerm, None))
                            (List.map (Option.map localDecl2) (ctrD.ins().getSameOrUpdateForOld ()))

                    let argsO = List.map localDeclTerm insO
                    let argsN = List.map localDeclTerm insN

                    let patO =
                        EConstructorApply(pO.child ctrO.name, [], argsO) // type parameters do not matter in a pattern

                    let patN =
                        EConstructorApply(pN.child ctrN.name, [], argsN)
                    // to share code between two cases below
                    // "case (p1,p2) -> body // comment" where vs_i are the variables in p_i
                    let buildCase (vars, pattern, comment, body) =
                        [ { vars = vars
                            patterns = [ pattern ]
                            body = ECommented(comment, body) } ]

                    match elem with
                    // no cases to generate for Delete, but we generate stubs for customization
                    | Diff.Add _ ->
                        if isForward then
                            // nothing to do
                            []
                        else
                            // case n -> ???
                            buildCase (insN, patN, "deleted constructor", missingTerm)
                    | Diff.Delete _ ->
                        if isForward then
                            // case o -> ???
                            buildCase (insO, patO, "deleted constructor", missingTerm)
                        else
                            // nothing to do
                            []
                    | Diff.Same _ ->
                        // case o -> o
                        buildCase (
                            (if isForward then insO else insN),
                            (if isForward then patO else patN),
                            "unchanged constructor",
                            EConstructorApply(
                                (if isForward then
                                     pN.child ctrN.name
                                 else
                                     pO.child ctrO.name),
                                [],
                                fst (List.unzip (if isForward then insT1 else insT2))
                            )
                        )
                    | Diff.Update _ ->
                        // for updates, we only generate the translations for the unchanged arguments
                        buildCase (
                            (if isForward then insO else insN),
                            (if isForward then patO else patN),
                            "added/deleted/updated constructor arguments",
                            EConstructorApply(
                                (if isForward then
                                     pN.child ctrN.name
                                 else
                                     pO.child ctrO.name),
                                [],
                                fst (List.unzip (if isForward then insT1 else insT2))
                            )
                        )

                let xO, xN = localDeclTerm xtO, localDeclTerm xtN
                let tO, tN = localDeclType xtO, localDeclType xtN

                let _, _, names = name p.name

                let body =
                    if tvsD.elements.IsEmpty
                       && ctrsD.isSame
                       && msD.isSame
                       && isJoint p then
                        // for joint datatypes with no type parameters, generate identity function
                        xO
                    else
                        EMatch(xO, tO, List.collect (mkCase true) ctrsD.elements, None)

                let body_back =
                    if tvsD.elements.IsEmpty
                       && ctrsD.isSame
                       && msD.isSame
                       && isJoint p then
                        // for joint datatypes with no type parameters, generate identity function
                        xN
                    else
                        EMatch(xN, tN, List.collect (mkCase false) ctrsD.elements, None)

                let translations =
                    Method(
                        IsFunction,
                        fst names,
                        typeParams,
                        inSpec,
                        outSpec,
                        [],
                        [],
                        [],
                        Some body,
                        false,
                        true,
                        false,
                        emptyMeta
                    )
                    :: (if config.generateBackwardTranslationFunctions then
                            [ Method(
                                  IsFunction,
                                  snd names,
                                  typeParams,
                                  inSpecBack,
                                  outSpecBack,
                                  [],
                                  [],
                                  [],
                                  Some body_back,
                                  false,
                                  true,
                                  false,
                                  emptyMeta
                              ) ]
                        else
                            [])

                let memberLemmas = decls ctxOb ctxNb msD
                // All paths to a lemma generated by a datatype function must insert "_bc" (already inserted elsewhere).
                // We cannot wrap all declarations generated by members into a module because
                // child modules cannot access anything in parent modules in Dafny.
                let namePrefix =
                    match nameD with
                    | SameName s -> s
                    | Rename (s, s1) -> s

                let memberLemmasWithPrefix =
                    List.map
                        (fun (d: Decl) ->
                            match d with
                            | Method (methodType,
                                      name,
                                      tpvars,
                                      ins,
                                      out,
                                      modifies,
                                      reads,
                                      decreases,
                                      body,
                                      ghost,
                                      isStatic,
                                      isOpaque,
                                      meta) ->
                                Method(
                                    methodType,
                                    namePrefix + "_" + name,
                                    tpvars,
                                    ins,
                                    out,
                                    modifies,
                                    reads,
                                    decreases,
                                    body,
                                    ghost,
                                    isStatic,
                                    isOpaque,
                                    meta
                                )
                            | _ -> d)
                        memberLemmas

                translations @ memberLemmasWithPrefix
            // immutable fields with initializer yield a lemma, mutable fields yield nothing
            | Diff.Field (_, tpD, dfD) when generateLemmaOrAxiomFor (p) ->
                match declO with
                | Field (_, _, dfO, _, isStatic, isMutable, _) when dfO.IsNone || not isStatic || isMutable -> []
                | Field (_, t, _, _, _, _, _) ->
                    if not tpD.isSame then
                        failwith (unsupported "change in type: " + p.ToString())

                    let tO, tN, tT =
                        match declN with
                        | Field (_, tN, _, _, _, _, _) -> tp (t, tN)
                        | _ -> failwith "impossible" // Diff.Field must occur with YIL.Field

                    let tT1, tT2 = tT

                    let recO, recN =
                        let parentO, parentN, _ = path (contextO.currentDecl)

                        let sr p =
                            StaticReceiver({ path = p; tpargs = [] })

                        sr parentO, sr parentN

                    let fieldsTranslation =
                        EEqual(tT1 (EMemberRef(recO, pO, [])), EMemberRef(recN, pN, [])), None

                    [ Method(
                          IsLemma,
                          pT.name + "_bc",
                          [],
                          InputSpec([], []),
                          OutputSpec([], [ fieldsTranslation ]),
                          [],
                          [],
                          [],
                          (if generateLemmaFor p then Some(EBlock []) else None),
                          true,
                          true,
                          false,
                          emptyMeta
                      ) ]
                | _ -> failwith "impossible" // Diff.Field must occur with YIL.Field
            | Diff.Field _ -> [] // unchanged fields produce nothing
            // Dafny functions produce lemmas; lemmas / Dafny methods produce nothing
            | Diff.Method (nameD, tvsD, insD, outsD, bdD) when generateLemmaOrAxiomFor (p) ->
                match declO, declN with
                | Method(methodType = IsLemma), _
                | Method(methodType = IsMethod), _ -> []
                | Method (_, _, tvs_o, ins_o, outs_o, modifiesO, readsO, decreasesO, bodyO, _, isStatic, isOpaqueO, _),
                  Method (_, _, tvs_n, ins_n, outs_n, modifiesN, readsN, decreasesN, _, _, _, isOpaqueN, _) ->
                    if not tvsD.isSameOrUpdated then
                        failwith (
                            unsupported "addition or deletion in type parameters: "
                            + p.ToString()
                        )

                    let ctxOh =
                        contextO
                            .enter(nameD.getOld)
                            .addTpvars (tvsD.getOld ())

                    let ctxNh =
                        contextN
                            .enter(nameD.getNew)
                            .addTpvars (tvsD.getNew ())

                    let ctxOi = ctxOh.add (insD.decls.getOld ())
                    let ctxNi = ctxNh.add (insD.decls.getNew ())

                    let ctxOb =
                        ctxOi.add(outsD.namedDecls.getOld ()).enterBody ()

                    let ctxNb =
                        ctxNi.add(outsD.namedDecls.getNew ()).enterBody ()
                    // we ignore changes in in/output conditions here and only compare declarations
                    // in fact, ensures clauses (no matter if changed) are ignored entirely
                    // we ignore changes in modifies, reads, decreases clauses
                    //
                    // as "methods", we only consider pure functions here
                    // a more general approach might also generate two-state lemmas for method invocations on class instances
                    // (i.e., calling corresponding methods with related arguments on related objects yields related values and
                    //   leaves the (possibly changed) objects related)
                    //
                    // For a static method without specification:
                    // method p<u,v>(x:a,y:u,z:u->v):B
                    //   requires some_property(x)
                    //   { ... }
                    // --->
                    // lemma p_bc<uO,uN,vO,vN>(u_forward:uO->uN, u_backward:uN->uO, v_forward:vO->vN, v_backward: vN->vO,
                    //   xO:aO, xN:aN, yO:uO, yN:uN, zO:uO->vO, zN:uN->vN)
                    //     requires some_property(xO)
                    //     requires xN == a_forward(xO)
                    //     requires yN == u_forward(yO)
                    //     (either)  requires forall x1_N: uN :: zN(x1_N) == v_forward(zO(u_backward(x1_N))
                    //     (or)      requires zN == ((x1_N:uN) => v_forward(zO(u_backward(x1_N))))
                    //     ensures some_property(xN)
                    //     ensures New.p(xN,uN)==B_forward(Old.p(xO,uO))
                    // and accordingly for the general case. If not static, the lemma additionally quantifies over the receivers.
                    //
                    // We change "requires some_property(xN)" to "ensures some_property(xN)" because
                    // we can easily prove false if we have "requires some_property(xO)", "requires some_property(xN)",
                    // "requires xN == a_forward(xO)", and a "slightly incorrect" function "a_forward".
                    // The function "a_forward" should be enough for proving "ensures some_property(xN)" from
                    // the precondition "requires some_property(xN)".
                    // The reason why we want to explicitly state this postcondition is we need to prove it when calling
                    // New.p(xN,uN) anyway, and Dafny sometimes cannot prove the precondition of New.p(xN,uN) if we
                    // did not state the postcondition explicitly.
                    let parentDeclO = contextO.lookupCurrent ()

                    let parentDeclN = contextN.lookupCurrent ()
                    // the following are only needed if the method is not static, but it's easier to compute them in any case
                    let parentTvs_o = parentDeclO.tpvars
                    let parentTvs_n = parentDeclN.tpvars
                    let parentO, parentN, parentT = path (contextO.currentDecl)

                    let parentTvsO, parentTvsN, parentTvsT =
                        List.unzip3 (List.map typearg2 (List.zip parentTvs_o parentTvs_n))

                    let oldInstDecl, newInstDecl, instancesTranslation =
                        let tO =
                            TApply(contextO.currentDecl, typeargsToTVars parentTvs_o)

                        let tN =
                            TApply(contextN.currentDecl, typeargsToTVars parentTvs_n)

                        localDecl2 (
                            LocalDecl(varname parentDeclO.name, tO, false),
                            LocalDecl(varname parentDeclN.name, tN, false)
                        )

                    let instanceInputs =
                        if isStatic then
                            []
                        else
                            [ oldInstDecl; newInstDecl ]

                    let receiverO, receiverN =
                        if isStatic then
                            // ignores the instances above
                            let sr p =
                                StaticReceiver({ path = p; tpargs = [] })

                            sr parentO, sr parentN
                        else
                            let objRec ld = ObjectReceiver(localDeclTerm ld, ld.tp)

                            objRec oldInstDecl, objRec newInstDecl
                    // the input types and arguments and the translations for the arguments
                    // parent type parameters and instanceInputs are empty if static
                    let tvsO, tvsN, tvsT =
                        List.unzip3 (List.map typearg2 (List.zip tvs_o tvs_n))

                    let typeParams =
                        Utils.listInterleave (parentTvsO @ tvsO, parentTvsN @ tvsN)
                    // old inputs and new inputs
                    let insO, _, _ =
                        List.unzip3 (List.map localDecl ins_o.decls)

                    let _, insN, _ =
                        List.unzip3 (List.map localDecl ins_n.decls)
                    // translations from old inputs to new inputs
                    let insO_translated, insN_translated, insT =
                        List.unzip3 (List.map localDecl2 (insD.decls.getSameOrUpdate ()))

                    let inputs =
                        instanceInputs
                        @ (if config.generateBackwardTranslationFunctions then
                               Utils.listInterleave (List.unzip parentTvsT)
                           else
                               List.map fst parentTvsT)
                          @ (if config.generateBackwardTranslationFunctions then
                                 Utils.listInterleave (List.unzip tvsT)
                             else
                                 List.map fst tvsT)
                            @ insO @ insN

                    // old requires clauses applied to old arguments
                    let oldHeaderCtx =
                        if isStatic then
                            ctxOh
                        else
                            ctxOh.setThisDecl (oldInstDecl)

                    let inputRequiresO =
                        ins_o.conditions
                        |> List.map
                            (fun c ->
                                let es = exprOld oldHeaderCtx Map.empty (fst c)
                                (es, snd c))

                    // new requires clauses become ensures arguments
                    let newInputCtx =
                        if isStatic then
                            ctxNi
                        else
                            ctxNi.setThisDecl (newInstDecl)

                    let inputEnsuresN =
                        ins_n.conditions
                        |> List.map
                            (fun c ->
                                let es = exprNew newInputCtx Map.empty (fst c)
                                (es, snd c))

                    // insT is (f1(old), f2(new))
                    // backward compatibility: new == f1(old)
                    let inputsTranslations =
                        if isStatic then
                            backward_compatible
                                insT
                                (List.map localDeclTerm insO_translated)
                                (List.map localDeclTerm insN_translated)
                        else
                            backward_compatible
                                (instancesTranslation :: insT)
                                (List.map localDeclTerm (oldInstDecl :: insO_translated))
                                (List.map localDeclTerm (newInstDecl :: insN_translated))

                    // lossless assumptions
                    let losslessAssumptions =
                        if config.generateBackwardTranslationFunctions then
                            List.map
                                (fun (tpargO: TypeArg, tparg_o: TypeArg, tparg_n: TypeArg) ->
                                    let _, _, tT =
                                        tp (TVar(fst tparg_o), TVar(fst tparg_n))

                                    lossless ctxOb (TVar(fst tpargO)) tT)
                                (List.zip3 (parentTvsO @ tvsO) (parentTvs_o @ tvs_o) (parentTvs_n @ tvs_n))
                        else
                            []

                    let inSpec =
                        InputSpec(
                            inputs,
                            inputRequiresO
                            @ inputsTranslations @ losslessAssumptions
                        )

                    // we don't need the ensures-conditions of the method
                    // because they can be proved from the verification of the method
                    // but we might add them if that helps

                    // the outputs and the translation function
                    let outputTypeT, outputTypeN, canTranslateOutput =
                        match outs_o, outs_n with
                        | OutputSpec ([], _), OutputSpec ([], _) -> None, None, true
                        | OutputSpec ([ hdO ], _), OutputSpec ([ hdN ], _) ->
                            try
                                let _, otN, otT = tp (hdO.tp, hdN.tp)
                                Some otT, Some otN, true
                            with _ -> None, None, false
                        | _ -> failwith (unsupported "multiple output declarations")

                    let resultO =
                        EMethodApply(receiverO, pO, typeargsToTVars tvsO, List.map localDeclTerm insO, true)

                    let resultN =
                        EMethodApply(receiverN, pN, typeargsToTVars tvsN, List.map localDeclTerm insN, true)

                    let outputsTranslation = backward_compatible_ensures outputTypeT outputTypeN canTranslateOutput resultO resultN
                    // in general for mutable classes, we'd also have to return that the receivers remain translated
                    // but that is redundant due to our highly restricted treatment of classes
                    // New inputs' ensures becomes "output spec" here because "input spec" contains requires
                    // and "output spec" contains ensures.
                    let outSpec =
                        OutputSpec([], inputEnsuresN @ [ outputsTranslation ])

                    // copy the decreases clause from the old implementation
                    let decreases = List.map (exprOld oldHeaderCtx Map.empty) decreasesO

                    let oldBodyCtx =
                        if isStatic then
                            ctxOb
                        else
                            ctxOb.setThisDecl (oldInstDecl)

                    let newBodyCtx =
                        if isStatic then
                            ctxNb
                        else
                            ctxNb.setThisDecl (newInstDecl)

                    // The body yields the proof of the lemma.
                    let proofBody =
                        if generateAxiomFor p then
                            None // an axiom
                        else
                            match bdD with
                            | Diff.SameExprO bdO ->
                                // unchanged body: try to generate proof sketch
                                // use oldCtx to replace "this" with old variables
                                //
                                // When bdO is None, both old and new functions are axioms.
                                // So we also generate axioms (body=None) in this case.
                                match outputTypeT with
                                | Some ot ->
                                    bdO
                                    |> Option.bind
                                        (fun b ->
                                            proof oldBodyCtx newBodyCtx Map.empty b resultO resultN (fst ot) isOpaqueO isOpaqueN)
                                | None -> Some(EBlock [])
                            | _ ->
                                // updated body: try to generate proof sketch
                                // use oldCtx to replace "this" with old variables
                                match bodyO with
                                | Some bd ->
                                    match outputTypeT with
                                    | Some ot -> proof oldBodyCtx newBodyCtx Map.empty bd resultO resultN (fst ot) isOpaqueO isOpaqueN
                                    | None -> Some(EBlock [])
                                | None ->
                                    // other cases: generate empty proof
                                    Some(EBlock [])
                    
                    let generatedLemma = Method(
                          IsLemma,
                          pT.name + "_bc",
                          typeParams,
                          inSpec,
                          outSpec,
                          [],
                          [],
                          decreases,
                          proofBody,
                          true,
                          true,
                          false,
                          emptyMeta
                      )
                    
                    let generatedSpecializedLemmas =
                        if config.specializeHigherOrderLemmas &&
                                Map.containsKey ctxOh.currentDecl specializedLemmas then
                            let invocations = Map.find ctxOh.currentDecl specializedLemmas |>
                                              List.distinctBy getSpecializedLemmaName
                            invocations |> List.map (fun e ->
                                let exprs =
                                    match e with
                                    | EMethodApply (receiver, method, tpargs, exprs, ghost) -> exprs
                                    | _ -> failwith "specialized lemma must come with EMethodApply"
                                let specializedLocations = getSpecializedArgumentLocations e
                                let filterInput ins = ins |> List.indexed |> List.filter (
                                    fun x -> List.contains (fst x) specializedLocations |> not) |> List.map snd
                                let specializedInputMap = ins_o.decls |> List.indexed |> List.filter (
                                    fun x -> List.contains (fst x) specializedLocations) |> List.map (
                                    fun (i, x) -> (x, exprs[i])) |> Map.ofList
                                let specializedLocalDeclTerm ld =
                                    Map.tryFind ld specializedInputMap |> Option.defaultValue (localDeclTerm ld)
                                
                                // inputs
                                let specializedInputs =
                                    instanceInputs
                                    @ (if config.generateBackwardTranslationFunctions then
                                           Utils.listInterleave (List.unzip parentTvsT)
                                       else
                                           List.map fst parentTvsT)
                                      @ (if config.generateBackwardTranslationFunctions then
                                             Utils.listInterleave (List.unzip tvsT)
                                         else
                                             List.map fst tvsT)
                                        @ (insO |> filterInput)
                                        @ (insN |> filterInput)
                                let specializedInputRequiresO =
                                    ins_o.conditions
                                    |> List.map
                                        (fun c ->
                                            let es = exprOld oldHeaderCtx specializedInputMap (fst c)
                                            (es, snd c))
                                
                                // translations from old inputs to new inputs
                                let insOexprs, insNexprs, insT =
                                    insD.decls.getSameOrUpdate()
                                    |> List.collect (fun (ldO, ldN) ->
                                        if specializedInputMap.ContainsKey(ldO) then
                                            [] // no need to require the translations for specialized inputs
                                        else
                                            localDecl2 (ldO, ldN)
                                            |> fun (x, y, z) -> [localDeclTerm x, localDeclTerm y, z])
                                    |> List.unzip3
                                let specializedInputsTranslations =
                                    if isStatic then
                                        backward_compatible
                                            insT
                                            insOexprs
                                            insNexprs
                                    else
                                        backward_compatible
                                            (instancesTranslation :: insT)
                                            (localDeclTerm oldInstDecl :: insOexprs)
                                            (localDeclTerm newInstDecl :: insNexprs)
                                let specializedInSpec =
                                    InputSpec(
                                        specializedInputs,
                                        specializedInputRequiresO
                                        @ specializedInputsTranslations @ losslessAssumptions
                                    )
                                
                                // the outputs
                                let specializedResultO =
                                    EMethodApply(receiverO, pO, typeargsToTVars tvsO,
                                                 ins_o.decls |> List.map (
                                                     fun ld -> exprOld ctxOh specializedInputMap (specializedLocalDeclTerm ld)), true)

                                let specializedResultN =
                                    EMethodApply(receiverN, pN, typeargsToTVars tvsN,
                                                 ins_n.decls |> List.map (
                                                     fun ld -> exprNew ctxNh specializedInputMap (specializedLocalDeclTerm ld)), true)

                                let specializedOutputsTranslation =
                                    backward_compatible_ensures outputTypeT outputTypeN canTranslateOutput specializedResultO specializedResultN
                                // in general for mutable classes, we'd also have to return that the receivers remain translated
                                // but that is redundant due to our highly restricted treatment of classes
                                // New inputs' ensures becomes "output spec" here because "input spec" contains requires
                                // and "output spec" contains ensures.
                                let outSpec =
                                    OutputSpec([], inputEnsuresN @ [ specializedOutputsTranslation ])
                                
                                // proof
                                let specializedProof =
                                    if generateAxiomForMethodApply e then
                                        None // an axiom
                                    else
                                        match bdD with
                                        | Diff.SameExprO bdO ->
                                            // unchanged body: try to generate proof sketch
                                            // use oldCtx to replace "this" with old variables
                                            //
                                            // When bdO is None, both old and new functions are axioms.
                                            // So we also generate axioms (body=None) in this case.
                                            match outputTypeT with
                                            | Some ot ->
                                                bdO
                                                |> Option.bind
                                                    (fun b ->
                                                        proof oldBodyCtx newBodyCtx specializedInputMap b specializedResultO specializedResultN (fst ot) isOpaqueO isOpaqueN)
                                            | None -> Some(EBlock [])
                                        | _ ->
                                            // updated body: try to generate proof sketch
                                            // use oldCtx to replace "this" with old variables
                                            match bodyO with
                                            | Some bd ->
                                                match outputTypeT with
                                                | Some ot -> proof oldBodyCtx newBodyCtx specializedInputMap bd specializedResultO specializedResultN (fst ot) isOpaqueO isOpaqueN
                                                | None -> Some(EBlock [])
                                            | None ->
                                                // other cases: generate empty proof
                                                Some(EBlock [])
                                Method(
                                  IsLemma,
                                  getSpecializedLemmaName e,
                                  typeParams,
                                  specializedInSpec,
                                  outSpec,
                                  [],
                                  [],
                                  decreases,
                                  specializedProof,
                                  true,
                                  true,
                                  false,
                                  emptyMeta
                                ))
                        else
                            []

                    generatedLemma :: generatedSpecializedLemmas
                | _ -> failwith ("impossible") // Diff.Method must occur with YIL.Method
            | Diff.Method _ -> [] // unchanged methods produce nothing
        /// generates the header info (types, specs) of the translation functions for a type declaration
        and typeDeclHeader (p: Path, dO: Decl, dN: Decl) =
            assert (dO.name = dN.name)
            typeDeclHeaderMain (p, dO.name, dO.tpvars, dN.tpvars)
        and typeDeclHeaderMain (p: Path, n: string, tvs_o: TypeArg list, tvs_n: TypeArg list) =
            let pO, pN, pT = path p

            let tvsO, tvsN, tvsT =
                List.unzip3 (List.map typearg2 (List.zip tvs_o tvs_n))

            let typeParams = Utils.listInterleave (tvsO, tvsN)
            let oldType = TApply(pO, typeargsToTVars tvsO)
            let newType = TApply(pN, typeargsToTVars tvsN)
            let xO, xN, _ = name (varname n)
            let xtO = LocalDecl(xO, oldType, false)
            let xtN = LocalDecl(xN, newType, false)

            let inputs =
                (if config.generateBackwardTranslationFunctions then
                     Utils.listInterleave (List.unzip tvsT)
                 else
                     List.map fst tvsT)
                @ [ xtO ]

            let inSpec = InputSpec(inputs, [])
            let outType = newType
            let outSpec = outputType (outType, [])

            let inputs_back =
                (if config.generateBackwardTranslationFunctions then
                     Utils.listInterleave (List.unzip tvsT)
                 else
                     List.map fst tvsT)
                @ [ xtN ]

            let inSpec_back = InputSpec(inputs_back, [])
            let outType_back = oldType
            let outSpec_back = outputType (outType_back, [])
            typeParams, inSpec, outSpec, xtO, xtN, inSpec_back, outSpec_back
        /// iterates LocalDecl-translation over a list and groups up the results
        and context(tpDs: Diff.TypeArgList,ldDs: Diff.LocalDeclList) : TypeArg list * LocalDecl list * (Condition * Condition) list =
            if tpDs.isSame && ldDs.isSame then
                let tps = tpDs.getSame ()
                let lds = ldDs.getSame ()
                let tpsO, tpsN, tpsT = List.unzip3 (List.map typearg tps)
                let ldsO, ldsN, ldsT = List.unzip3 (List.map localDecl lds)

                Utils.listInterleave (tpsO, tpsN),
                (fst (List.unzip tpsT))
                @ Utils.listInterleave (ldsO, ldsN),
                ldsT
            else
                failwith (unsupported "change in type/term arguments")
        /// translates a local decl: x:A --->  xO: AO, xN: AN, 
        and localDecl (ld: LocalDecl) : LocalDecl * LocalDecl * (Condition * Condition) =
            let nO, nN, _ = name ld.name
            let tO, tN, tT = tp (ld.tp, ld.tp)
            let g = ld.ghost
            LocalDecl(nO, tO, g), LocalDecl(nN, tN, g), (((fst tT) (EVar nO), None), ((snd tT) (EVar nN), None))
        and localDecl2 (ldO: LocalDecl, ldN: LocalDecl) : LocalDecl * LocalDecl * (Condition * Condition) =
            let nO, nN, _ = name2 (ldO.name, ldN.name)
            let tO, tN, tT = tp (ldO.tp, ldN.tp)
            LocalDecl(nO, tO, ldO.ghost),
            LocalDecl(nN, tN, ldN.ghost),
            (((fst tT) (EVar nO), None), ((snd tT) (EVar nN), None))
        and listOfFuncToFuncOfList (l: (Expr -> Expr) List) =
            (fun x -> List.map (fun (a, b) -> a b) (List.zip l x))
        and diag (x: Expr, y: Expr) = EEqual(x, y)
        and reduce (e: Expr) = Traverser.reduce (ctxO, e)
        and abstractRel (x: string, tO: Type, tN: Type, body: Expr -> Expr) : Expr =
            let xOE = EVar x
            let bodyXOE = body xOE
            let abs = EFun([ LocalDecl(x, tO, false) ], None, tN, bodyXOE)
            reduce abs // reduce eta-contracts
        and notExpr (e: Expr) : Expr =
            match e with
            | EUnOpApply ("Not", arg) -> arg // remove "!" if there is one
            | _ -> EUnOpApply ("Not", e) // add "!" if there is not one
        /// translates built-in types
        and tpBuiltinTypes (tO: Type, tN: Type) : Type * Type * ((Expr -> Expr) * (Expr -> Expr)) =
            let realToInt eReal tReal tInt =
                EMemberRef(ObjectReceiver(eReal, tReal), Path [ "Floor" ], [])
            match tO, tN with
            | TUnit, TUnit
            | TBool, TBool
            | TInt _, TInt _
            | TNat _, TNat _
            | TChar, TChar
            | TString _, TString _
            | TReal _, TReal _
            | TBitVector _, TBitVector _
            | TObject, TObject -> tO, tN, (id, id)
            | TInt _, TReal _ -> tO, tN, ((fun e -> ETypeConversion(e, tN)), (fun e -> realToInt e tN tO))
            | TReal _, TInt _ -> tO, tN, ((fun e -> realToInt e tO tN), (fun e -> ETypeConversion(e, tO)))
            | _ ->
                failwith (
                    unsupported "trying to translate "
                    + tO.ToString()
                    + " to another type: "
                    + tN.ToString()
                )
        /// inductively extends the translation of type names to complex types
        /// a --->  aO, aN, a_forward, a_backward
        /// the translation functions are produced as meta-expressions to use F# for simplification
        /// because they are usually only needed applied to arguments
        /// if they are needed unapplied, they must be wrapped in YIL-lambdas.
        and tp (tO: Type, tN: Type) : Type * Type * ((Expr -> Expr) * (Expr -> Expr)) =
            match tO with
            | TUnit
            | TBool
            | TInt _
            | TNat _
            | TChar
            | TString _
            | TReal _
            | TBitVector _
            | TObject -> tpBuiltinTypes (tO, tN)
            | TVar a ->
                match tN with
                | TVar b ->
                    let aO, aN, aT = name2 (a, b)
                    // apply the function of the type variable to the old/new value
                    TVar aO,
                    TVar aN,
                    ((fun e -> EAnonApply(EVar(fst aT), [ e ])), (fun e -> EAnonApply(EVar(snd aT), [ e ])))
                | _ ->
                    failwith (
                        unsupported "trying to translate "
                        + tO.ToString()
                        + " to another type: "
                        + tN.ToString()
                    )
            | TApply (p_o, ts_o) ->
                let p_n, ts_n =
                    match tN with
                    | TApply (p_n, ts_n) when ts_o.Length = ts_n.Length -> p_n, ts_n
                    // || ts_o.Length + ts_n.Length = 1 -> p_n, ts_n
                    // TODO: prepend proper type translation functions for the case ts_o.Length + ts_n.Length = 1
                    // where one type is a simple wrapper of the other
                    | _ ->
                        failwith (
                            unsupported "trying to translate "
                            + tO.ToString()
                            + " to another type: "
                            + tN.ToString()
                        )

                let parO = p_o.parent
                let parN = p_n.parent
                let pO, _, _ = path p_o
                let _, pN, _ = path p_n
                let _, _, names = name2 (p_o.name, p_n.name)

                let rO =
                    StaticReceiver({ path = parO; tpargs = [] })

                let rN =
                    StaticReceiver({ path = parN; tpargs = [] })

                let tsONT =
                    if ts_o.Length = 0 && ts_n.Length = 1 then
                        [ tp (tO, List.head ts_n) ] // assume the new type is a wrapper of the old type
                    else if ts_o.Length = 1 && ts_n.Length = 0 then
                        [ tp (List.head ts_o, tN) ] // same
                    else
                        List.map tp (List.zip ts_o ts_n)

                let tsT =
                    List.map (fun (o, n, (t1, t2)) -> (abstractRel ("x", o, n, t1), abstractRel ("x", n, o, t2))) tsONT

                let tsT1, tsT2 = List.unzip tsT

                let tsTs =
                    if config.generateBackwardTranslationFunctions then
                        Utils.listInterleave (tsT1, tsT2)
                    else
                        tsT1

                let tsO, tsN, _ = List.unzip3 tsONT

                TApply(pO, tsO),
                TApply(pN, tsN),
                if isJointType (tO, tN) then
                    (id, id)
                else
                    ((fun x -> EMethodApply(rO, parO.child (fst names), tsO, tsTs @ [ x ], false)),
                     (fun x -> EMethodApply(rN, parN.child (snd names), tsN, tsTs @ [ x ], false)))
            | TTuple ts_o ->
                match tN with
                | TTuple ts_n ->
                    // element-wise translations on tuples
                    assert (ts_o.Length = ts_n.Length)

                    let tsO, tsN, tsT =
                        List.unzip3 (List.map tp (List.zip ts_o ts_n))

                    let its = List.indexed tsT

                    let T1 x =
                        let esT1 =
                            its
                            |> List.map (fun (i, (t1, _)) -> t1 (reduce (EProj(x, i)))) // reduce eliminates projections from tuples

                        ETuple(esT1) // tuple of component mappings

                    let T2 x =
                        let esT2 =
                            its
                            |> List.map (fun (i, (_, t2)) -> t2 (reduce (EProj(x, i)))) // reduce eliminates projections from tuples

                        ETuple(esT2) // tuple of component mappings

                    TTuple tsO, TTuple tsN, (T1, T2)
                | _ ->
                    failwith (
                        unsupported "trying to translate "
                        + tO.ToString()
                        + " to another type: "
                        + tN.ToString()
                    )
            | TFun (ts_o, u_o) ->
                match tN with
                | TFun (ts_n, u_n) ->
                    // translate functions
                    // x1:t1, ..., xn:tn
                    let lds_o =
                        List.indexed ts_o
                        |> List.map (fun (i, t) -> LocalDecl("x" + (i + 1).ToString(), t, false))

                    let lds_n =
                        List.indexed ts_n
                        |> List.map (fun (i, t) -> LocalDecl("x" + (i + 1).ToString(), t, false))
                    // ldsO = x1O:t1O, ..., xnO:tnO
                    // ldsN = x1N:t1N, ..., xnN:tnN
                    // ldsT = t1-translations(x1O,x1N), ..., tN-translations(xnO,xnN)
                    let ldsO, ldsN, ldsT =
                        List.unzip3 (List.map localDecl2 (List.zip lds_o lds_n))

                    let ldsT1, ldsT2 = List.unzip ldsT // unused... is ldsT1 the same as T1 inputsO?
                    let inputTypesO = List.map localDeclType ldsO
                    let inputTypesN = List.map localDeclType ldsN
                    let inputsO = List.map localDeclTerm ldsO
                    let inputsN = List.map localDeclTerm ldsN
                    // input type translation functions
                    let tsO, tsN, tsT =
                        List.unzip3 (List.map tp (List.zip ts_o ts_n))

                    let its = List.indexed tsT

                    let T1 x =
                        List.map (fun ((t1, _), x) -> t1 x) (List.zip tsT x)

                    let T2 x =
                        List.map (fun ((_, t2), x) -> t2 x) (List.zip tsT x)
                    // output type translation functions
                    let outputTypeO, outputTypeN, (outputT1, outputT2) = tp (u_o, u_n)
                    // To translate fO(xO) to fN(xN), we need to translate xN to xO, apply fO,
                    // then translate the result to outputTypeN
                    let funsTranslation1 fO =
                        let varsN = inputsN
                        let varsO = T2 varsN
                        let bodyO = EAnonApply(fO, varsO)
                        let bodyN = outputT1 bodyO
                        EFun(ldsN, None, outputTypeN, bodyN)

                    let funsTranslation2 fN =
                        let varsO = inputsO
                        let varsN = T1 varsO
                        let bodyN = EAnonApply(fN, varsN)
                        let bodyO = outputT2 bodyN
                        EFun(ldsO, None, outputTypeO, bodyO)

                    TFun(inputTypesO, outputTypeO), TFun(inputTypesN, outputTypeN), (funsTranslation1, funsTranslation2)
                | _ ->
                    failwith (
                        unsupported "trying to translate "
                        + tO.ToString()
                        + " to another type: "
                        + tN.ToString()
                    )
            | TNullable t_o ->
                match tN with
                | TNullable t_n ->
                    let tOa, tNa, tT = tp (t_o, t_n)

                    let tT1 =
                        fun x -> EIf(EEqual(x, ENull tOa), ENull tNa, Some((fst tT) x))

                    let tT2 =
                        fun x -> EIf(EEqual(x, ENull tNa), ENull tOa, Some((snd tT) x))

                    TNullable tOa, TNullable tNa,
                    if isJointType (tO, tN) then
                        (id, id)
                    else
                        (tT1, tT2)
                | _ ->
                    failwith (
                        unsupported "trying to translate "
                        + tO.ToString()
                        + " to another type: "
                        + tN.ToString()
                    )
            | TSeq (b_o, t_o) ->
                match tN with
                | TSeq (b_n, t_n) ->
                    let tOa, tNa, tT = tpAbstracted ("sq", t_o, t_n)
                    TSeq(b_o, tOa), TSeq(b_n, tNa),
                    if isJointType (tO, tN) then
                        (id, id)
                    else
                        (seqRel tOa tNa (fst tT), seqRel tNa tOa (snd tT))
                | _ ->
                    failwith (
                        unsupported "trying to translate "
                        + tO.ToString()
                        + " to another type: "
                        + tN.ToString()
                    )
            | TSet (b_o, t_o) ->
                match tN with
                | TSet (b_n, t_n) ->
                    let tOa, tNa, tT = tpAbstracted ("st", t_o, t_n)
                    TSet(b_o, tOa), TSet(b_n, tNa),
                    if isJointType (tO, tN) then
                        (id, id)
                    else
                        (setRel tOa tNa (fst tT), setRel tNa tOa (snd tT))
                | _ ->
                    failwith (
                        unsupported "trying to translate "
                        + tO.ToString()
                        + " to another type: "
                        + tN.ToString()
                    )
            | TMap (b_o, s_o, t_o) ->
                match tN with
                | TMap (b_n, s_n, t_n) ->
                    let sO, sN, sT = tpAbstracted ("mp", s_o, s_n)
                    let tOa, tNa, tT = tpAbstracted ("mp", t_o, t_n)

                    TMap(b_o, sO, tOa),
                    TMap(b_n, sN, tNa),
                    if isJointType (tO, tN) then
                        (id, id)
                    else
                        ((mapRel sO sN sT tOa tNa tT), (mapRel sN sO (snd sT, fst sT) tNa tOa (snd tT, fst tT)))
                | _ ->
                    failwith (
                        unsupported "trying to translate "
                        + tO.ToString()
                        + " to another type: "
                        + tN.ToString()
                    )
            | TArray (b_o, n_o, t_o) ->
                match tN with
                | TArray (b_n, n_n, t_n) ->
                    let tOa, tNa, tT = tpAbstracted ("ar", t_o, t_n)
                    TArray(b_o, n_o, tOa), TArray(b_n, n_n, tNa),
                    if isJointType (tO, tN) then
                        (id, id)
                    else
                        (arrayRel tOa tNa (fst tT), arrayRel tNa tOa (snd tT))
                | _ ->
                    failwith (
                        unsupported "trying to translate "
                        + tO.ToString()
                        + " to another type: "
                        + tN.ToString()
                    )
            | TUnimplemented -> TUnimplemented, TUnimplemented, ((fun _ -> EUnimplemented), (fun _ -> EUnimplemented))
        and tpAbstracted (x: string, t_o: Type, t_n: Type) =
            let tO, tN, tT = tp (t_o, t_n)
            tO, tN, (abstractRel (x, tO, tN, (fst tT)), abstractRel (x, tN, tO, (snd tT)))
        /// inductively extends the translation of paths to expressions, returning the OLD expression
        and exprOld (exprCtx: Context) (ldmap: Map<LocalDecl, Expr>) (e: Expr) : Expr =
            NameTranslator(true, ldmap)
                .expr (
                    exprCtx.translateLocalDeclNames
                        (fun (n: LocalDecl) ->
                            if ldmap.ContainsKey(n) then
                                n.name
                            else
                                let nO, _, _ = name n.name
                                nO),
                    e
                )
        /// inductively extends the translation of paths to expressions, returning the NEW expression
        and exprNew (exprCtx: Context) (ldmap: Map<LocalDecl, Expr>) (e: Expr) : Expr =
            NameTranslator(false, ldmap)
                .expr (
                    exprCtx.translateLocalDeclNames
                        (fun (n: LocalDecl) ->
                            if ldmap.ContainsKey(n) then
                                n.name
                            else
                                let _, nN, _ = name n.name
                                nN),
                    e
                )

        /// entry point for running the translation
        member this.doTranslate() = decls ctxO ctxN declsD


    /// entry point to call translator on a module --- experimental, unused
    /// assumes the module is at the program toplevel
    /// dependency analysis is done at the intramodule level, with granularity of every decl child of the module.
    /// precondition: (m, mD) is a valid translation pair.
    /// Joint.X ---> Old.X
    ///  |            |
    ///  V            V
    /// New.X  ---> Translations.X
    /// where X is the name of a module in the original program.
    /// Modules Joint.X are shared among old and new program. Modules Old.X and New.X occur
    /// in only one of the two (add or delete) or both (update).
    /// This method
    /// - computes the set of declarations in the Joint part
    /// - generates the Translations part.
    /// A subsequent step is expected to copy the old and new program and prefix the names in all toplevel
    /// declarations with either "Joint." or "New.", resp. "Old.".
    let translateModule (ctxO: Context, ctxN: Context, pD: Diff.Decl) =
        let ctxOm = ctxO.enter (pD.name.getOld) // enter decl of m
        let ctxNm = ctxN.enter (pD.name.getNew) // enter decl of m

        let inputOk (nameO: string) (nameD: Diff.Name) =
            match nameD with
            | Diff.SameName s -> nameO = s
            | Diff.Rename (o, n) -> nameO = o

        match pD with
        | Diff.Module (nameD, declD) ->
            let pathOfOld =
                fun (decl: Decl) -> Path [ nameD.getOld; decl.name ]

            let mO = ctxOm.lookupCurrent ()

            let childPaths = List.map pathOfOld mO.children
            let sameChildren = List.map pathOfOld (declD.getSame ())

            let changedChildren =
                Utils.listDiff (childPaths, sameChildren)

            let changedClosed =
                Analysis.dependencyClosure (ctxOm, mO.children, changedChildren)

            let jointPaths =
                Utils.listDiff (childPaths, changedClosed)

            Console.WriteLine($" ***** DEPENDENCY CLOSURE FOR {mO.name} *****")
            List.iter (fun (Path x) -> Console.WriteLine(String.concat ", " x)) changedClosed
            Console.WriteLine($" ***** JOINT PATHS FOR {mO.name} *****")
            List.iter (fun (p: Path) -> Console.WriteLine((p.ToString()))) jointPaths
            Console.WriteLine($" ***** JOINT PATHS FOR {mO.name} END *****")

            let tr = Translator(ctxOm, ctxNm, declD, jointPaths, Set.empty, Set.empty, Map.empty, defaultConfig)

            tr.doTranslate (), jointPaths
        | _ -> failwith "declaration to be translated is not a module"

    /// prints a list of paths
    let printPaths (kind: string, ps: Path list) =
        Console.WriteLine("********* " + kind + " *****")
        List.iter (fun x -> Console.WriteLine(x.ToString())) ps
        Console.WriteLine("***** END " + kind + " *****")

    /// entry point for translating a program
    let prog (pO: Program, pN: Program, newName: string, pD: Diff.Program, config: TranslatorConfig) : Program * Path list =
        let ctxO = Context(pO)
        let pathOf (d: Decl) = ctxO.currentDecl.child (d.name)
        let childPaths = List.map pathOf pO.decls // toplevel paths of p
        let sameChildren = List.map pathOf (pD.decls.getSame ()) // the unchanged ones among those

        let changedChildren =
            Utils.listDiff (childPaths, sameChildren) // the changed ones

        let changedClosed =
            Analysis.dependencyClosure (ctxO, pO.decls, changedChildren) // dependency closure of the changed ones

        let jointPaths =
            Utils.listDiff (childPaths, changedClosed) // greatest self-contained set of unchanged declarations

        printPaths ("unchanged", sameChildren)
        printPaths ("changed", changedChildren)
        printPaths ("affected (dependency closure of changed)", changedClosed)
        printPaths ("joint", jointPaths)

        let changedInOld =
            DiffAnalysis.changedInOld (Context(pO), Context(pN), pD)

        printPaths ("affected in old", Set.toList changedInOld)
        
        let calledByAffectedInOld =
            Analysis.GatherPathsUsedByPaths(changedInOld).gather pO
        
        printPaths ("directly called by affected in old", Set.toList calledByAffectedInOld)
        
        let isJoint (p: Path) : bool =
            List.exists (fun (j: Path) -> j.isAncestorOf p) jointPaths
        
        // A copy of the function in "type Translator"
        let generateLemmaOrAxiomFor (p: Path) : bool =
            config.alwaysGenerateLemmas || changedInOld.Contains(p)
            || (config.generateAxiomsForUnchanged && (not (isJoint p)) && calledByAffectedInOld.Contains(p))
        
        // higher-order function calls with a changed function argument
        // a map from higher-order functions to a list of invocations (EMethodApply) where
        // each invocation has at least one changed function argument
        let mutable specializedCalls : Map<Path, Expr list> = Map.empty
        let specializedLemmas =
            DiffAnalysis.GatherSpecializedLemmaToGenerate(generateLemmaOrAxiomFor).gather(Context(pO), Context(pN), pD)

        let tr =
            Translator(
                Context(pO),
                Context(pN),
                pD.decls,
                jointPaths,
                changedInOld,
                calledByAffectedInOld,
                specializedLemmas,
                config
            )

        let translations =
            { name = newName
              decls = tr.doTranslate ()
              meta = emptyMeta }

        translations, jointPaths
