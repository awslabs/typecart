namespace TypeInjections

open YIL

/// Defines wrappers for standard Dafny functions
module DafnyFunctions =
    /// maps f over sequence f
    let seqMap s f = EUnimplemented
    /// maps f over sequence s
    let setMap s f = EUnimplemented
    /// maps f over keys and g over values in map m
    let mapMap m f g = EUnimplemented
    /// maps f over an array a
    let arrayMap a f = EUnimplemented

open DafnyFunctions

// variable naming conventions:
//  xD: diff between two x's
//  xT: translation of x

/// takes a diff between two YIL objects and returns the translation declarations/objects for it
module Translation =
  let unsupported s = "unsupported: " + s
  
  /// translates a program, encapsulates global data/state for use during translation
  type Translator(prog: Program, progD: Diff.Program, jointDecls: Path list) =
    /// convenience for iteration over a list of declarations
    let rec decls (context: Context) (dsD: Diff.List<Decl, Diff.Decl>) =
        List.collect (decl context) dsD.elements

    /// translates one declaration
    and decl (context: Context) (dD: Diff.Elem<Decl, Diff.Decl>) : Decl list =
        match dD with
        | Diff.Same d -> declSame context d
        | Diff.Add _
        | Diff.Delete _ -> []  // nothing to generate for added/deleted declarations
        | Diff.Update(dif) -> declUpdate context dif

    /// translates an unchanged declaration
    and declSame (context: Context)(d: Decl) : Decl list =
        let p = context.currentDecl.child (d.name)
        let pO, pN, pT = path (p)
        let contextInner = context.enter(d.name)

        match d with
        | Module _
        | Datatype _ ->
            // these can be treated as special of changed declarations that happen not to have changes
            declUpdate context (Diff.idDecl d)
        | Class _
        | ClassConstructor _ ->
            // these are not supported yet
            failwith (unsupported "classes")
        | Export _ -> [d] // TODO check
        | DUnimplemented -> [DUnimplemented]
        // the declarations where we actually do something special
        | TypeDef (_, _, super, _, isNew, _) ->
            // TypeDefs produce methods
            let typeParams, inSpec, outSpec, xtO, xtN = typeDeclHeader (p, d)
            let xO = localDeclTerm xtO
            let xN = localDeclTerm xtN

            let body =
                if isNew then
                    // new types are new primitive types, so diagonal
                    EEqual(xO, xN)
                else
                    // otherwise, call relation of supertype
                    let _, _, superT = tp super
                    superT (xO, xN)

            [ Method(false, pT.name, typeParams, inSpec, outSpec, Some body, false, true, emptyMeta) ]
        // methods produce lemmas; lemmas produce nothing
        | Method(isLemma = true) -> []
        | Method (_, _, tvs, ins, outs, bodyO, _, isStatic, _) ->
            // as "methods", we only consider pure functions here
            // a more general approach might also generate two-state lemmas for method invocations on class instances
            // (i.e., calling corresponding methods with related arguments on related objects yields related values and
            //   leaves the (possibly changed) objects related)
            //
            // method p<u>(x:a,y:u):B = {_} --->
            // lemma  p<uO,uN,vO,vN>(uT:uO*uN->bool, vT:vO*vN->bool, xO:aO, xN:aN, yO:uO, yN:uN))
            //     requires a-related(xO,xN) && uT(yO,yN)
            //     ensures B-related(pO(xO,uO), pN(xN, uN)
            // and accordingly for the general case. If not static, we additionally need arguments for the receiver.
            let parentDecl = context.lookupCurrent ()
            // the following are only needed if the method is not static, but it's easier to compute them in any case
            let parentTvs = parentDecl.tpvars
            let parentO, parentN, parentT = path (context.currentDecl)

            let parentTvsO, parentTvsN, parentTvsT =
                if isStatic then
                    [], [], []
                else
                    List.unzip3 (List.map typearg parentTvs)

            let oldInstDecl, newInstDecl, instancesRelated =
                localDecl (LocalDecl(varname parentDecl.name, TApply(context.currentDecl, List.map TVar parentTvs), false))

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
            // the input types and arguments and the conditions that the latter are related
            // parent type parameters and instanceInputs are empty if static
            let tvsO, tvsN, tvsT = List.unzip3 (List.map typearg tvs)

            let typeParams =
                Utils.listInterleave (parentTvsO @ tvsO, parentTvsN @ tvsN)

            let insO, insN, insT =
                match ins with
                | InputSpec (lds, _) -> List.unzip3 (List.map localDecl lds)

            let inputs =
                instanceInputs
                @ parentTvsT
                  @ tvsT @ Utils.listInterleave (insO, insN)

            let inputsRelated =
                if isStatic then
                    insT
                else
                    instancesRelated :: insT

            let inSpec = InputSpec(inputs, inputsRelated)
            // the outputs and the condition that they're related
            let _, _, outputTypeT =
                match outs with
                | OutputType (t, _) -> tp t
                | OutputDecls _ -> failwith (unsupported "methods")

            let resultO =
                EMethodApply(receiverO, pO, List.map TVar tvsO, List.map localDeclTerm insO, true)

            let resultN =
                EMethodApply(receiverN, pN, List.map TVar tvsN, List.map localDeclTerm insN, true)

            let outputsRelated = outputTypeT (resultO, resultN)
            let outSpec = OutputDecls([], [ outputsRelated ])
            // The body yields the proof of the lemma.
            let proof =
                bodyO
                |> Option.bind (fun b -> let _, _, pf = expr b in pf)

            [ Method(true, pT.name, typeParams, inSpec, outSpec, proof, true, true, emptyMeta) ]
        // immutable fields with initializer yield a lemma, mutable fields yield nothing
        | Field (_, _, dfO, _, isStatic, isMutable, _) when dfO.IsNone || not isStatic || isMutable -> []
        | Field (_, t, _, _, _, _, _) ->
            let tO, tN, tT = tp t

            let recO, recN =
                let parentO, parentN, _ = path (context.currentDecl)

                let sr p =
                    StaticReceiver({ path = p; tpargs = [] })

                sr parentO, sr parentN

            let fieldsRelated =
                tT (EMemberRef(recO, pO, []), EMemberRef(recN, pN, []))

            [ Method(
                  true,
                  pT.name,
                  [],
                  InputSpec([], []),
                  OutputDecls([], [ fieldsRelated ]),
                  None,
                  true,
                  true,
                  emptyMeta
              ) ]

    /// translates a changed declaration
    and declUpdate (context: Context)(dif: Diff.Decl) : Decl list =
        let n = match dif.name with
                | Diff.SameName n -> n
                | Diff.Rename _ -> failwith (unsupported "renamed declaration")
        let p = context.currentDecl.child(n)
        let pO, pN, pT = path p
        let ctxI = context.enter(n)
        match dif with
        | Diff.Class _
        | Diff.ClassConstructor _ -> failwith (unsupported "change in classes")
        | Diff.TypeDef _
        | Diff.Method _
        | Diff.Field _
        | Diff.Export _
        | Diff.DUnimplemented -> failwith(unsupported "change in atomic declaration")
        | Diff.Module (_, msD) ->
            [ Module(n, decls ctxI msD, emptyMeta) ]
        | Diff.Datatype (_, tvsD, ctrsD, msD) ->
            if not tvsD.isSame then
                failwith (unsupported "change in type parameters")
            let tvs = tvsD.getSame
            // datatype p.name<u,v> = con1(a,u) | con2(b,v) --->
            // datatype pO<uO,vO> = con1(aO,uO) | con2(bO,vO)
            // datatype pN<uN,vN> = con1(aN,uN) | con2(bN,vN)
            // function pT<uO,uN,vO,vN>(uT:uO*uN->bool, vT:vO*vN->bool, xO:pO(uO,vO), xN:pN(uN,vN)) = match xO,xN
            //   | con1(x1,x2), con1(y1,y2) => aT(x1,y1) && uT(x2,y2)
            //   | con2(x1,x2), con2(y1,y2) => bT(x1,y1) && vT(x2,y2)
            //   | _ -> false
            // and accordingly for the general case.
            let typeParams, inSpec, outSpec, xtO, xtN = typeDeclHeaderMain (p, n, tvs)

            let mkCase ctrD =
                match ctrD with
                | Diff.Add _
                | Diff.Delete _ -> [] // no cases to generate
                | Diff.Update ctrU -> failwith(unsupported "change in constructor")
                | Diff.Same ctr ->
                    let insO, insN, insT =
                        List.unzip3 (List.map localDecl ctr.ins)

                    let argsO = List.map localDeclTerm insO
                    let argsN = List.map localDeclTerm insN
                    let cn = ctr.name

                    let patO =
                        EConstructorApply(pO.child (cn), [], argsO) // type parameters do not matter in a pattern

                    let patN =
                        EConstructorApply(pN.child (cn), [], argsN)

                    [{ vars = Utils.listInterleave (insO, insN)
                       pattern = ETuple([ patO; patN ])
                       body = EConj(insT) }]

            let dflt = EBool false
            let xO, xN = localDeclTerm xtO, localDeclTerm xtN
            let tO, tN = localDeclType xtO, localDeclType xtN

            let body =
                EMatch(ETuple [ xO; xN ], TTuple [ tO; tN ], List.collect mkCase ctrsD.elements, Some dflt)

            let relation =
                Method(false, pT.name, typeParams, inSpec, outSpec, Some body, false, true, emptyMeta)

            let memberLemmas = decls ctxI msD
            relation :: memberLemmas

    // joint code for type declarations
    and typeDeclHeader(p: Path, d: Decl) = typeDeclHeaderMain(p, d.name, d.tpvars) 
    and typeDeclHeaderMain(p: Path, n:string, tvs: TypeArg list) =
        let pO, pN, pT = path p
        let tvsO, tvsN, tvsT = List.unzip3 (List.map typearg tvs)
        let typeParams = Utils.listInterleave (tvsO, tvsN)
        let oldType = TApply(pO, List.map TVar tvsO)
        let newType = TApply(pN, List.map TVar tvsN)
        let xO, xN, _ = name (varname n)
        let xtO = LocalDecl(xO, oldType, false)
        let xtN = LocalDecl(xN, newType, false)
        let inputs = tvsT @ [ xtO; xtN ]
        let inSpec = InputSpec(inputs, [])
        let outSpec = OutputType(TBool, [])
        typeParams, inSpec, outSpec, xtO, xtN

    /// translates a context, e.g., the arguments of a polymorphic method
    /// Ideally, we would translate type and term variables individually and collect the results.
    /// But type variables give rise to both type and term variables,
    /// and term variables give rise to both term variables and preconditions,
    /// which cannot alternate in a Dafny context.
    /// Therefore, we translate them at once using multiple outputs.
    and context (tpDs: Diff.TypeArgList, ldDs: Diff.LocalDeclList) : TypeArg list * LocalDecl list * Condition list =
        if tpDs.isSame && ldDs.isSame then
            let tps = tpDs.getSame
            let lds = ldDs.getSame
            let tpsO, tpsN, tpsT = List.unzip3 (List.map typearg tps)
            let ldsO, ldsN, ldsT = List.unzip3 (List.map localDecl lds)
            Utils.listInterleave (tpsO, tpsN), tpsT @ Utils.listInterleave (ldsO, ldsN), ldsT
        else
            failwith (unsupported "change in type/term arguments")

    /// old, new, and combine path for a path
    // This is the only place that uses the literal prefix strings.
    and path (p: Path) : Path * Path * Path =
        let prefixRoot (p: Path) (s: string) =
            Path((s + "." + p.names.Head) :: p.names.Tail)
        // joint decls are the same in old and new version
        // the combine declaration is still generated because e.g., a joint type can be called with non-joint type parameters
        if List.exists (fun (j:Path) -> j.isAncestorOf p) jointDecls then
           (prefixRoot p "Joint", prefixRoot p "Joint", prefixRoot p "Combine")
        else
           (prefixRoot p "Old", prefixRoot p "New", prefixRoot p "Combine")

    /// suggests a name for a variable of the type defined by a declaration name
    and varname (n:string) = n.Chars(0).ToString()

    /// s ---> s_old, s_new, s
    // This is the only place that uses the literal names.
    and name (s: string) = "old_" + s, "new_" + s, s

    /// a --->  a_old, a_new, a: a_old * a_new -> bool
    and typearg (a: TypeArg) : TypeArg * TypeArg * LocalDecl =
        let aO, aN, aT = name a
        aO, aN, LocalDecl(aT, TFun([ TVar aO ], TVar aN), false)

    /// x:a ---> x_old: a_old, x_new: a_new, requires a(x_old,x_new)
    and localDecl (ld: LocalDecl) : LocalDecl * LocalDecl * Condition =
        let nO, nN, nT = name ld.name
        let tO, tN, tT = tp ld.tp
        let g = ld.ghost
        LocalDecl(nO, tO, g), LocalDecl(nN, tN, g), tT (EVar nO, EVar nN)

    /// diagonal relation
    and diag (x: Expr, y: Expr) = EEqual(x, y)
    /// convenience for building a lambda-abstraction
    and abstractRel (x: string, tO: Type, tN: Type, body: Expr * Expr -> Expr) =
        let xO, xN, _ = name (x)

        EFun(
            [ LocalDecl(xO, tO, false)
              LocalDecl(xN, tN, false) ],
            TBool,
            body (EVar(xO), EVar(xN))
        )
    /// tp(t) = (o,n,f) such that o/n are the old/new types corresponding to t and f:n->o is the translation function
    and tp (t: Type) : Type * Type * (Expr * Expr -> Expr) =
        match t with
        | TUnit
        | TBool
        | TInt
        | TNat
        | TChar
        | TString
        | TReal
        | TBitVector _ -> t, t, diag
        | TVar a ->
            let aO, aN, aT = name a
            TVar aO, TVar aN, (fun (e, f) -> EAnonApply(EVar aT, [ e; f ]))
        | TApply (p, ts) ->
            let pO, pN, pT = path p

            let r =
                StaticReceiver({ path = pT.parent; tpargs = [] })

            let tsONT = List.map tp ts

            let tsT =
                List.map (fun (o, n, t) -> abstractRel ("x", o, n, t)) tsONT

            let tsO, tsN, _ = List.unzip3 tsONT
            let tsON = Utils.listInterleave (tsO, tsN)
            TApply(pO, tsO), TApply(pN, tsN), (fun (x, y) -> EMethodApply(r, pT, tsON, tsT @ [ x; y ], false))
        | TTuple ts ->
            // two tuples are related if all elements are
            let tsO, tsN, tsT = List.unzip3 (List.map tp ts)

            let T (x, y) =
                match x, y with
                | ETuple xs, ETuple ys ->
                    // optimization to avoid reducible expressions
                    let txys = List.zip3 tsT xs ys

                    let eTs =
                        List.map (fun (t, x, y) -> t (x, y)) txys

                    EConj(eTs)
                | _ ->
                    let its = List.indexed tsT

                    let esT =
                        List.map (fun (i, t) -> t (EProj(x, i), EProj(y, i))) its

                    EConj(esT)

            TTuple tsO, TTuple tsN, T
        | TFun (ts, u) ->
            // two functions are related if they map related arguments to related results
            // x1:t1, ..., xn:tn
            let lds =
                List.indexed ts
                |> List.map (fun (i, t) -> LocalDecl("x" + (i + 1).ToString(), t, false))
            // ldsO = x1O:t1O, ..., xnO:tnO
            // ldsN = x1N:t1N, ..., xnO:tnN
            // ldsT = t1-related(x1O,x1N), ..., tN-related(xnO,xnN)
            let ldsO, ldsN, ldsT = List.unzip3 (List.map localDecl lds)
            let inputTypesO = List.map localDeclType ldsO
            let inputTypesN = List.map localDeclType ldsN
            let outputTypeO, outputTypeN, outputTypeRelationn = tp u
            let inputDecls = Utils.listInterleave (ldsO, ldsN)
            let inputsO = List.map localDeclTerm ldsO
            let inputsN = List.map localDeclTerm ldsN
            let inputsRelated = EConj(ldsT)

            let funsRelated (o, n) =
                let outputO = EAnonApply(o, inputsO)
                let outputN = EAnonApply(n, inputsN)
                let outputRelated = outputTypeRelationn (outputO, outputN)
                EQuant(Forall, inputDecls, Some(inputsRelated), outputRelated)

            TFun(inputTypesO, outputTypeO), TFun(inputTypesN, outputTypeN), funsRelated
        | TObject ->
            // TODO: check if t,t,diag is sound here
            // alternatively, check if bisimulation works
            failwith (unsupported "object type")
        | TSeq t ->
            let tO, tN, tT = tp t
            TSeq tO, TSeq tN, (fun e -> seqMap e tT)
        | TSet t ->
            let tO, tN, tT = tp t
            TSet tO, TSet tN, (fun e -> setMap e tT)
        | TMap (s, t) ->
            let sO, sN, sT = tp s
            let tO, tN, tT = tp t
            TMap(sO, tO), TMap(sN, tN), (fun e -> mapMap e sT tT)
        | TArray t ->
            let tO, tN, tT = tp t
            TArray tO, TArray tN, (fun e -> arrayMap e tT)
        | TUnimplemented -> TUnimplemented, TUnimplemented, (fun _ -> EUnimplemented)

    /// translates expression e:t to the proof that it is an t-related
    ///
    /// if |- e:t and tp t = tO, tN, tT, then
    /// post(expr(e,t) = eO,eN,eT where eT is a proof of tT(eO,eN)
    /// Dafny does not have full proof terms and finds proofs automatically.
    /// So it's not clear what can/should return here.
    /// But we probably have to return the instances of the lemmas generated by the methods used in e.
    /// For now, we return None so that we can call the function already.
    and expr (e: Expr) : Expr * Expr * (Expr option) = EUnimplemented, EUnimplemented, None

    member this.doProg() = decls (Context prog) progD.decls
    
  /// entry point to call the translator on a program
  /// the resulting program consists of 4 parts
  /// Joint.X ---> Old.X
  ///  |            |
  ///  V            V
  /// New.X  ---> Combine.X
  /// where X is the name of a module of the original program
  /// This method generates the Combine-part and returns the set of joint declarations of Old and New.
  /// A subsequent step is expected to copy the old and new program and prefix the names in all toplevel
  /// declarations with "Joint.", "New.", resp. "Old.".
  let prog (p: Program, pD: Diff.Program) : Program * Path list =
    let ctx = Context(p)
    let pathOf(d: Decl) = ctx.currentDecl.child(d.name)
    let childPaths = List.map pathOf p.decls
    let sameChildren = List.map pathOf pD.decls.getSame
    let changedChildren = Utils.listDiff(childPaths, sameChildren)
    let changedClosed = Analysis.dependencyClosure(ctx, p.decls, changedChildren)
    // greatest self-contained set of unchanged declarations
    let jointPaths = Utils.listDiff(childPaths, changedClosed)
    let tr = Translator(p,pD,jointPaths)
    { name = p.name; decls = tr.doProg()}, jointPaths
