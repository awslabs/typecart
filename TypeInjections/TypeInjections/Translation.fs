namespace TypeInjections

open System
open TypeInjections.Diff
open TypeInjections.YIL
open YIL

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

    /// translates a program, encapsulates global data/state for use during translation
    type Translator(ctx: Context, declsD: Diff.DeclList, jointDecls: Path list) =
        /// old, new, and translations path for a path
        // This is the only place that uses the literal prefix strings.
        let rec path (p: Path) : Path * Path * Path =
            // joint decls are the same in old and new version
            // the translation declaration is still generated because e.g.,
            // a joint type can be called with non-joint type parameters
            if isJoint p then
                (p.prefix "Joint", p.prefix "Joint", p)
            else
                (p.prefix "Old", p.prefix "New", p)
        and isJoint (p: Path) : bool =
            List.exists (fun (j: Path) -> j.isAncestorOf p) jointDecls
        and name (s: string) =
            // old variable name, new variable name,
            // (forward translation function name, backward translation function name)
            s + "_O", s + "_N", (s + "_forward", s + "_backward")
        and name2 (s: string, t: string) =
            // old variable name, new variable name,
            // (forward translation function name, backward translation function name)
            s + "_O",
            t + "_N",
            if s = t then
                (s + "_forward", s + "_backward")
            else
                (s + "_to_" + t, t + "_back_to_" + s)
        and typearg (a: TypeArg) : TypeArg * TypeArg * (LocalDecl * LocalDecl) =
            let v = snd a
            let aO, aN, aT = name (fst a)

            (aO, v),
            (aN, v),
            (LocalDecl(fst aT, TFun([ TVar aO ], TVar aN), false), LocalDecl(snd aT, TFun([ TVar aN ], TVar aO), false))
        and typearg2 (a: TypeArg, b: TypeArg) : TypeArg * TypeArg * (LocalDecl * LocalDecl) =
            if a = b then
                typearg a
            else
                let nameO, nameN, nameT = name2 (fst a, fst b)

                (nameO, snd a),
                (nameN, snd b),
                (LocalDecl(fst nameT, TFun([ TVar nameO ], TVar nameN), false),
                 LocalDecl(snd nameT, TFun([ TVar nameN ], TVar nameO), false))
        and varname (n: string) = n.Chars(0).ToString()
        and NameTranslator (old: bool) =
            { new Traverser.Identity() with
                override this.path(ctx: Context, p: Path) =
                    let pO, pN, _ = path p
                    if old then pO else pN

                override this.expr(ctx: Context, e: Expr) =
                    match e with
                    | EVar n ->
                        if ctx.lookupLocalDeclO(n).IsSome then
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
        and backward_compatible (insT: (Expr * Expr) list) (insN: LocalDecl list) : Expr list =
            List.map (fun ((f1, f2), inN: LocalDecl) -> EEqual(EVar(inN.name), f1)) (List.zip insT insN)
        and lossless (tO: Type) (tT: (Expr -> Expr) * (Expr -> Expr)) : Expr =
            // forall x1_O: U_O :: U_back(U(x1_O)) == x1_O
            let nO, _, _ = name "x"
            let ld = LocalDecl(nO, tO, true)
            EQuant(Forall, [ ld ], None, EEqual((snd tT) ((fst tT) (EVar nO)), EVar nO))
        and decls (context: Context) (dsD: Diff.List<Decl, Diff.Decl>) =
            List.collect (decl context) dsD.elements
        and decl (context: Context) (dD: Diff.Elem<Decl, Diff.Decl>) : Decl list =
            match dD with
            | Diff.Same d -> declSameOrUpdate context (d, d) (Diff.idDecl d)
            | Diff.Add _
            | Diff.Delete _ -> [] // nothing to generate for added/deleted declarations
            | Diff.Update (d, n, df) -> declSameOrUpdate context (d, n) df
        and declSameOrUpdate (context: Context) (declO: Decl, declN: Decl) (dif: Diff.Decl) : Decl list =
            let n =
                match dif.name with
                | Diff.SameName n -> n
                | Diff.Rename _ -> failwith (unsupported "renamed declaration")

            let p = context.currentDecl.child (n)
            let pO, pN, pT = path p
            let ctxI = context.enter (n)

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
            | Diff.Module (_, msD) -> [ Module(n, decls ctxI msD, context.currentMeta ()) ]
            | Diff.TypeDef (_, tvsD, superD, exprD) ->
                match declO with
                | TypeDef (_, _, super, _, isNew, _) ->
                    // TypeDefs produce methods
                    let typeParams, inSpec, outSpec, xtO, xtN, inSpecBack, outSpecBack =
                        typeDeclHeader (p, declO, declN)

                    let xO = localDeclTerm xtO
                    let xN = localDeclTerm xtN

                    let body =
                        if isNew then
                            // new types are new primitive types, so return identity map
                            // but we may need explicit type conversion
                            ETypeConversion(xO, xtN.tp)
                        else
                            match declN with
                            | TypeDef (_, _, superN, _, _, _) ->
                                // otherwise, call function of supertype
                                let _, _, superT = tp (super, superN)
                                (fst superT) xO
                            | _ -> failwith "impossible" // Diff.TypeDef must go with YIL.TypeDef

                    let body_back =
                        if isNew then
                            // new types are new primitive types, so return identity map
                            // but we may need explicit type conversion
                            ETypeConversion(xN, xtO.tp)
                        else
                            match declN with
                            | TypeDef (_, _, superN, _, _, _) ->
                                // otherwise, call function of supertype
                                let _, _, superT = tp (super, superN)
                                (snd superT) xN
                            | _ -> failwith "impossible" // Diff.TypeDef must go with YIL.TypeDef

                    let _, _, names = name p.name

                    [ Method(
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
                        context.currentMeta ()
                      )
                      Method(
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
                          context.currentMeta ()
                      ) ]
                | _ -> failwith ("impossible") // Diff.TypeDef must go with YIL.TypeDef

            | Diff.Datatype (nameD, tvsD, ctrsD, msD) ->
                // generate translation functions

                if not tvsD.isSameOrUpdated then
                    failwith (
                        unsupported "addition or deletion in type parameters: "
                        + p.ToString()
                    )

                let tvsO =
                    match declO with
                    | Datatype (_, tpvars, _, _, _) -> tpvars
                    | _ -> failwith ("impossible") // Diff.Datatype must go with YIL.Datatype

                let tvsN =
                    match declN with
                    | Datatype (_, tpvars, _, _, _) -> tpvars
                    | _ -> failwith ("impossible") // Diff.Datatype must go with YIL.Datatype

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

                    let _, _, insT =
                        List.unzip3 (List.map localDecl2 (ctrD.ins().getSameOrUpdate ()))

                    let insT1, insT2 = List.unzip insT
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
                            pattern = pattern
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
                                (if isForward then insT1 else insT2)
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
                                (if isForward then insT1 else insT2)
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
                    [ Method(
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
                        emptyMeta
                      )
                      Method(
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
                          emptyMeta
                      ) ]

                let memberLemmas = decls ctxI msD
                // All paths to a lemma generated by a datatype function must insert "_Lemma".
                // We cannot wrap all declarations generated by members into a module because
                // child modules cannot access anything in parent modules in Dafny.
                let namePrefix =
                    match nameD with
                    | SameName s -> s
                    | Rename (s, s1) -> s

                let memberLemmasWithLemmaSuffix =
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
                                      meta) ->
                                Method(
                                    methodType,
                                    namePrefix + "_" + name + "_Lemma",
                                    tpvars,
                                    ins,
                                    out,
                                    modifies,
                                    reads,
                                    decreases,
                                    body,
                                    ghost,
                                    isStatic,
                                    meta
                                )
                            | _ -> d)
                        memberLemmas

                translations @ memberLemmasWithLemmaSuffix
            // immutable fields with initializer yield a lemma, mutable fields yield nothing
            | Diff.Field (_, tpD, dfD) ->
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
                        let parentO, parentN, _ = path (context.currentDecl)

                        let sr p =
                            StaticReceiver({ path = p; tpargs = [] })

                        sr parentO, sr parentN

                    let fieldsTranslation =
                        EEqual(tT1 (EMemberRef(recO, pO, [])), EMemberRef(recN, pN, []))

                    [ Method(
                          IsLemma,
                          pT.name,
                          [],
                          InputSpec([], []),
                          OutputSpec([], [ fieldsTranslation ]),
                          [],
                          [],
                          [],
                          Some(EBlock []),
                          true,
                          true,
                          emptyMeta
                      ) ]
                | _ -> failwith "impossible" // Diff.Field must occur with YIL.Field
            // Dafny functions produce lemmas; lemmas / Dafny methods produce nothing
            | Diff.Method (_, tvsD, insD, outsD, bdD) ->
                match declO, declN with
                | Method(methodType = IsLemma), _
                | Method(methodType = IsMethod), _ -> []
                | Method (_, _, tvs_o, ins_o, outs_o, modifiesO, readsO, decreasesO, bodyO, _, isStatic, _),
                  Method (_, _, tvs_n, ins_n, outs_n, modifiesN, readsN, decreasesN, _, _, _, _) ->
                    if not tvsD.isSameOrUpdated then
                        failwith (
                            unsupported "addition or deletion in type parameters: "
                            + p.ToString()
                        )
                    // we ignore changes in in/output conditions here and only compare declarations
                    // in fact, ensures clauses (no matter if changed) are ignored entirely
                    (*if not (insD.decls.getUpdate().IsEmpty) then
                        failwith (
                            unsupported "update to individual inputs: "
                            + p.ToString()
                        )

                    if not outsD.decls.isSame then
                        failwith (unsupported "change in outputs: " + p.ToString())*)
                    // if modifies, reads, decreases clauses change, throw an error
                    // TODO here
                    // as "methods", we only consider pure functions here
                    // a more general approach might also generate two-state lemmas for method invocations on class instances
                    // (i.e., calling corresponding methods with related arguments on related objects yields related values and
                    //   leaves the (possibly changed) objects related)
                    //
                    // For a static method without specification:
                    // method p<u,v>(x:a,y:u,z:u->v):B = {_} --->
                    // lemma p<uO,uN,vO,vN>(uT:uO->uN, uT_back:uN->uO, vT:vO->vN, xO:aO, xN:aN, yO:uO, yN:uN, zO:uO->vO, zN:uN->vN))
                    //     requires xN==aT(xO)
                    //     requires yN==uT(yO)
                    //     requires ((x1_N:uN) => vT(zO(uT_back(x1_N)))) == zN
                    //     ensures pN(xN,uN)==BT(pO(xO,uO))
                    // and accordingly for the general case. If not static, the lemma additionally quantifies over the receivers.
                    let parentDecl = context.lookupCurrent ()
                    // the following are only needed if the method is not static, but it's easier to compute them in any case
                    let parentTvs_o = parentDecl.tpvars
                    let parentO, parentN, parentT = path (context.currentDecl)

                    let parentTvsO, parentTvsN, parentTvsT =
                        if isStatic then
                            [], [], []
                        else
                            List.unzip3 (List.map typearg parentTvs_o) // TODO: typearg2 parentTvs_o parentTvs_n

                    let oldInstDecl, newInstDecl, instancesTranslation =
                        let t =
                            TApply(context.currentDecl, typeargsToTVars parentTvs_o)

                        localDecl (LocalDecl(varname parentDecl.name, t, false))

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
                            let objRec ld = ObjectReceiver(localDeclTerm ld)
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
                    let _, insN_translated, insT =
                        List.unzip3 (List.map localDecl2 (insD.decls.getSameOrUpdate ()))

                    // TODO: remove unused backward translation functions
                    let inputs =
                        instanceInputs
                        @ (Utils.listInterleave (List.unzip parentTvsT))
                          @ (Utils.listInterleave (List.unzip tvsT))
                            @ insO @ insN

                    // old requires clauses applied to old arguments
                    let oldCtx =
                        if isStatic then
                            ctx
                        else
                            ctx.setThisDecl (oldInstDecl)

                    let inputRequiresO, _ =
                        ins_o.conditions
                        |> List.map (fun c -> expr oldCtx c)
                        |> List.unzip

                    // new requires clauses applied to new arguments
                    let newCtx =
                        if isStatic then
                            ctx
                        else
                            ctx.setThisDecl (newInstDecl)

                    let _, inputRequiresN =
                        ins_n.conditions
                        |> List.map (fun c -> expr newCtx c)
                        |> List.unzip

                    // insT is (f1(old), f2(new))
                    // backward compatibility: new == f1(old)
                    let inputsTranslations =
                        if isStatic then
                            backward_compatible insT insN_translated
                        else
                            backward_compatible (instancesTranslation :: insT) (newInstDecl :: insN_translated)

                    // lossless assumptions
                    let losslessAssumptions =
                        List.map
                            (fun (tpargO: TypeArg, tparg_o: TypeArg, tparg_n: TypeArg) ->
                                let _, _, tT =
                                    tp (TVar(fst tparg_o), TVar(fst tparg_n))

                                lossless (TVar(fst tpargO)) tT)
                            (List.zip3 (parentTvsO @ tvsO) (parentTvs_o @ tvs_o) (parentTvs_o @ tvs_n)) // TODO: parentTvs_n @ tvs_n

                    let inSpec =
                        InputSpec(
                            inputs,
                            inputRequiresO
                            @ inputRequiresN
                              @ inputsTranslations @ losslessAssumptions
                        )

                    // we don't need the ensures-conditions of the method
                    // because they can be proved from the verification of the method
                    // but we might add them if that helps

                    // the outputs and the translation function
                    let outputTypeT =
                        match outs_o, outs_n with
                        | OutputSpec ([], _), OutputSpec ([], _) -> None
                        | OutputSpec ([ hdO ], _), OutputSpec ([ hdN ], _) ->
                            let _, _, ot = tp (hdO.tp, hdN.tp)
                            Some ot
                        | _ -> failwith (unsupported "multiple output declarations")

                    let resultO =
                        EMethodApply(receiverO, pO, typeargsToTVars tvsO, List.map localDeclTerm insO, true)

                    let resultN =
                        EMethodApply(receiverN, pN, typeargsToTVars tvsN, List.map localDeclTerm insN, true)

                    let outputsTranslation =
                        match outputTypeT with
                        | Some ot -> EEqual(resultN, (fst ot) resultO)
                        | None -> EBool true
                    // in general for mutable classes, we'd also have to return that the receivers remain translated
                    // but that is redundant due to our highly restricted treatment of classes
                    let outSpec = OutputSpec([], [ outputsTranslation ])

                    // The body yields the proof of the lemma.
                    let proof =
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
                                |> Option.bind (fun b -> proof oldCtx b resultN (fst ot))
                            | None -> Some(EBlock [])
                        | _ ->
                            // updated body: try to generate proof sketch
                            // use oldCtx to replace "this" with old variables
                            match bodyO with
                            | Some bd ->
                                match outputTypeT with
                                | Some ot -> proof oldCtx bd resultN (fst ot)
                                | None -> Some(EBlock [])
                            | None ->
                                // other cases: generate empty proof
                                Some(EBlock [])

                    [ Method(IsLemma, pT.name, typeParams, inSpec, outSpec, [], [], [], proof, true, true, emptyMeta) ]
                | _ -> failwith ("impossible") // Diff.Method must occur with YIL.Method
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

            let inputs = (fst (List.unzip tvsT)) @ [ xtO ]
            let inSpec = InputSpec(inputs, [])
            let outType = newType
            let outSpec = outputType (outType, [])

            let inputs_back = (snd (List.unzip tvsT)) @ [ xtN ]
            let inSpec_back = InputSpec(inputs_back, [])
            let outType_back = oldType
            let outSpec_back = outputType (outType_back, [])
            typeParams, inSpec, outSpec, xtO, xtN, inSpec_back, outSpec_back
        and context
            (
                tpDs: Diff.TypeArgList,
                ldDs: Diff.LocalDeclList
            ) : TypeArg list * LocalDecl list * (Condition * Condition) list =
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
        and localDecl (ld: LocalDecl) : LocalDecl * LocalDecl * (Condition * Condition) =
            let nO, nN, _ = name ld.name
            let tO, tN, tT = tp (ld.tp, ld.tp)
            let g = ld.ghost
            LocalDecl(nO, tO, g), LocalDecl(nN, tN, g), ((fst tT) (EVar nO), (snd tT) (EVar nN))
        and localDecl2 (ldO: LocalDecl, ldN: LocalDecl) : LocalDecl * LocalDecl * (Condition * Condition) =
            let nO, nN, _ = name2 (ldO.name, ldN.name)
            let tO, tN, tT = tp (ldO.tp, ldN.tp)
            LocalDecl(nO, tO, ldO.ghost), LocalDecl(nN, tN, ldN.ghost), ((fst tT) (EVar nO), (snd tT) (EVar nN))
        and listOfFuncToFuncOfList (l: (Expr -> Expr) List) =
            (fun x -> List.map (fun (a, b) -> a b) (List.zip l x))
        and diag (x: Expr, y: Expr) = EEqual(x, y)
        and reduce (e: Expr) = Traverser.reduce (ctx, e)
        and abstractRel (x: string, tO: Type, tN: Type, body: Expr -> Expr) =
            let xO, _, _ = name (x)
            let xOE = EVar xO
            let bodyXOE = body xOE

            let abs =
                EFun([ LocalDecl(xO, tO, false) ], tN, bodyXOE)

            reduce abs // reduce eta-contracts
        and tpBuiltinTypes (tO: Type, tN: Type) : Type * Type * ((Expr -> Expr) * (Expr -> Expr)) =
            let realToInt eReal tInt =
                EMemberRef(ObjectReceiver(eReal), Path [ "Floor" ], [])

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
            | TInt _, TReal _ -> tO, tN, ((fun e -> ETypeConversion(e, tN)), (fun e -> realToInt e tO))
            | TReal _, TInt _ -> tO, tN, ((fun e -> realToInt e tN), (fun e -> ETypeConversion(e, tO)))
            | _ ->
                failwith (
                    unsupported "trying to translate "
                    + tO.ToString()
                    + " to another type: "
                    + tN.ToString()
                )
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
                    | TApply (p_n, ts_n) -> p_n, ts_n
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

                let rO = StaticReceiver({ path = parO; tpargs = [] })
                let rN = StaticReceiver({ path = parN; tpargs = [] })

                let tsONT = List.map tp (List.zip ts_o ts_n)

                let tsT =
                    List.map (fun (o, n, (t1, t2)) -> (abstractRel ("x", o, n, t1), abstractRel ("x", o, n, t2))) tsONT

                let tsT1, tsT2 = List.unzip tsT
                let tsO, tsN, _ = List.unzip3 tsONT

                TApply(pO, tsO),
                TApply(pN, tsN),
                ((fun x -> EMethodApply(rO, parO.child (fst names), tsO, tsT1 @ [ x ], false)),
                 (fun x -> EMethodApply(rN, parN.child (snd names), tsN, tsT2 @ [ x ], false)))
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
                        EFun(ldsN, outputTypeN, bodyN)

                    let funsTranslation2 fN =
                        let varsO = inputsO
                        let varsN = T1 varsO
                        let bodyN = EAnonApply(fN, varsN)
                        let bodyO = outputT2 bodyN
                        EFun(ldsO, outputTypeO, bodyO)

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
                    let tO, tN, tT = tp (t_o, t_n)

                    let tT1 =
                        fun x -> EIf(EEqual(x, ENull tO), ENull tN, Some((fst tT) x))

                    let tT2 =
                        fun x -> EIf(EEqual(x, ENull tN), ENull tO, Some((snd tT) x))

                    TNullable tO, TNullable tN, (tT1, tT2)
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
                    let tO, tN, tT = tpAbstracted ("sq", t_o, t_n)
                    TSeq(b_o, tO), TSeq(b_n, tN), (seqRel tO tN (fst tT), seqRel tN tO (snd tT))
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
                    let tO, tN, tT = tpAbstracted ("st", t_o, t_n)
                    TSet(b_o, tO), TSet(b_n, tN), (setRel tO tN (fst tT), setRel tN tO (snd tT))
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
                    let tO, tN, tT = tpAbstracted ("mp", t_o, t_n)

                    TMap(b_o, sO, tO),
                    TMap(b_n, sN, tN),
                    ((mapRel sO sN sT tO tN tT), (mapRel sN sO (snd sT, fst sT) tN tO (snd tT, fst tT)))
                | _ ->
                    failwith (
                        unsupported "trying to translate "
                        + tO.ToString()
                        + " to another type: "
                        + tN.ToString()
                    )
            | TArray (b_o, t_o) ->
                match tN with
                | TArray (b_n, t_n) ->
                    let tO, tN, tT = tpAbstracted ("ar", t_o, t_n)
                    TArray(b_o, tO), TArray(b_n, tN), (arrayRel tO tN (fst tT), arrayRel tN tO (snd tT))
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
        and expr (exprCtx: Context) (e: Expr) : Expr * Expr =
            let eO = NameTranslator(true).expr (exprCtx, e)
            let eN = NameTranslator(false).expr (exprCtx, e)
            eO, eN
        and proof (oldCtx: Context) (e: Expr) (resultN: Expr) (resultOTranslation: Expr -> Expr) : Expr option =
            // generate proof for backward compatibility theorem
            let eO = NameTranslator(true).expr (oldCtx, e)
            Some(EBlock [ EAssert(EEqual(resultN, resultOTranslation eO)) ])

        /// entry point for running the translation
        member this.doTranslate() = decls ctx declsD


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
    let translateModule (ctx: Context, m: Decl, pD: Diff.Decl) =
        let ctx = ctx.enter (m.name) // enter decl of m

        let inputOk (nameO: string) (nameD: Diff.Name) =
            match nameD with
            | Diff.SameName s -> nameO = s
            | Diff.Rename (o, n) -> nameO = o

        match m, pD with
        | Module _ as m, Diff.Module (nameD, declD) when (inputOk m.name nameD) ->
            let pathOf =
                fun (decl: Decl) -> Path [ m.name; decl.name ]

            let childPaths = List.map pathOf m.children
            let sameChildren = List.map pathOf (declD.getSame ())

            let changedChildren =
                Utils.listDiff (childPaths, sameChildren)

            let changedClosed =
                Analysis.dependencyClosure (ctx, m.children, changedChildren)

            let jointPaths =
                Utils.listDiff (childPaths, changedClosed)

            Console.WriteLine($" ***** DEPENDENCY CLOSURE FOR {m.name} *****")
            List.iter (fun (Path x) -> Console.WriteLine(String.concat ", " x)) changedClosed
            Console.WriteLine($" ***** JOINT PATHS FOR {m.name} *****")
            List.iter (fun (p: Path) -> Console.WriteLine((p.ToString()))) jointPaths
            Console.WriteLine($" ***** JOINT PATHS FOR {m.name} END *****")

            let tr = Translator(ctx, declD, jointPaths)

            tr.doTranslate (), jointPaths
        | _ -> failwith "declaration to be translated is not a module"

    /// prints a list of paths
    let printPaths (kind: string, ps: Path list) =
        Console.WriteLine("********* " + kind + " *****")
        List.iter (fun x -> Console.WriteLine(x.ToString())) ps
        Console.WriteLine("***** END " + kind + " *****")

    /// entry point for translating a program
    let prog (p: Program, newName: string, pD: Diff.Program) : Program * Path list =
        let ctx = Context(p)
        let pathOf (d: Decl) = ctx.currentDecl.child (d.name)
        let childPaths = List.map pathOf p.decls // toplevel paths of p
        let sameChildren = List.map pathOf (pD.decls.getSame ()) // the unchanged ones among those

        let changedChildren =
            Utils.listDiff (childPaths, sameChildren) // the changed ones

        let changedClosed =
            Analysis.dependencyClosure (ctx, p.decls, changedChildren) // dependency closure of the changed ones

        let jointPaths =
            Utils.listDiff (childPaths, changedClosed) // greatest self-contained set of unchanged declarations

        printPaths ("unchanged", sameChildren)
        printPaths ("changed", changedChildren)
        printPaths ("dependency closure of changed", changedClosed)
        printPaths ("joint", jointPaths)

        let tr =
            Translator(Context(p), pD.decls, jointPaths)

        let translations =
            { name = newName
              decls = tr.doTranslate ()
              meta = emptyMeta }

        translations, jointPaths
