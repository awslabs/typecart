namespace TypeInjections

open System
open TypeInjections.Traverser
open YIL

/// Wrappers for standard Dafny functions that we assume to exist; need to be written and added to yucca
module DafnyFunctions =
    let rb = Path ["util"; "RelateBuiltinTypes"]
    let rbRec = StaticReceiver {path=rb; tpargs=[]}
    /// given relation t on o*n, the sequences e: seq<n> and f:seq<n> are related
    /// if they have the same length and are related element-wise
    let seqRel o n t (e,f) = EBool true // EMethodApply(rbRec, rb.child("seq"), [o;n], [t;e;f], false)
    /// given relation t on o*n, the array e: arr<n> and f:arr<n> are related
    /// if they have the same length and are related element-wise
    let arrayRel o n t (e,f) = EBool true // EMethodApply(rbRec, rb.child("array"), [o;n], [t;e;f], false)
    /// given relation t on o*n, the sets e: set<n> and f:set<n> are related
    /// if every element of e is related to an element of f and vice versa
    let setRel o n t (e,f) = EBool true // EMethodApply(rbRec, rb.child("set"), [o;n], [t;e;f], false)
    /// given relations, sT,tT on so*sn and tO*tN, the maps e: map<sO,tO> and f:map<sN,tN> are related
    /// if every pair in e is related a pair in f and vice versa
    let mapRel sO sN sT tO tN tT (e,f) = EBool true // EMethodApply(rbRec, rb.child("map"), [sO;sN;tO;tN], [sT;tT;e;f], false)
    /// option types.
    /// Option<T> and Option<U> are related if T and U are related and both are Some _ or both are None.
    let optionRel o n t (e, f) = EMethodApply(rbRec, rb.child("option"), [o;n], [t;e;f], false)

open DafnyFunctions

// variable naming conventions:
//  xD: diff between two x's
//  xT: translation of x

/// takes a diff between two YIL objects and returns the translation declarations/objects for it
module Translation =
  let unsupported s = "unsupported: " + s
  
  /// translates a program, encapsulates global data/state for use during translation
  type Translator(prog: Program, progD: Diff.Program, jointDecls: Path list) =

    /// old, new, and combine path for a path
    // This is the only place that uses the literal prefix strings.
    let rec path (p: Path) : Path * Path * Path =
        let prefixRoot (p: Path) (s: string) =
            Path((s + "." + p.names.Head) :: p.names.Tail)
        // joint decls are the same in old and new version
        // the combine declaration is still generated because e.g., a joint type can be called with non-joint type parameters
        if List.exists (fun (j:Path) -> j.isAncestorOf p) jointDecls then
           (prefixRoot p "Joint", prefixRoot p "Joint", prefixRoot p "Combine")
        else
           (prefixRoot p "Old", prefixRoot p "New", prefixRoot p "Combine")

    /// s ---> s_old, s_new, s
    // This is the only place that uses the literal names.
    and name (s: string) = s+"_O", s+"_N", s

    /// a --->  a_old, a_new, a: a_old * a_new -> bool
    and typearg (a: TypeArg) : TypeArg * TypeArg * LocalDecl =
        let v = snd a
        let aO, aN, aT = name (fst a)
        (aO,v), (aN,v), LocalDecl(aT, TFun([ TVar aO ], TVar aN), false)

    /// suggests a name for a variable of the type defined by a declaration name
    and varname (n:string) = n.Chars(0).ToString()
      
    /// translates paths and type/expr variables to old or new variant
    // empty context must be passed so that traversal context tracks local bindings
    and NameTranslator(old: bool) =
         {new Identity() with
            override this.path(ctx: Context, p: Path) =
                let pO,pN,_ = path p
                if old then pO else pN
            override this.expr(ctx: Context, e: Expr) =
                match e with
                | EVar n ->
                    if ctx.lookupLocalDeclO(n).IsSome then
                      e // locally bound variables are not translated
                    else
                      let nO,nN,_ = name n
                      EVar(if old then nO else nN)
                | _ -> this.exprDefault(ctx, e)
            override this.tp(ctx: Context, t: Type) =
                match t with
                | TVar n ->
                    let nO,nN,_ = typearg (n,None)
                    TVar(if old then fst nO else fst nN)
                | _ -> this.tpDefault(ctx, t)
        }
    
    /// convenience for iteration over a list of declarations
    and decls (context: Context) (dsD: Diff.List<Decl, Diff.Decl>) =
        List.collect (decl context) dsD.elements

    /// translates one declaration
    and decl (context: Context) (dD: Diff.Elem<Decl, Diff.Decl>) : Decl list =
        match dD with
        | Diff.Same d -> declSameOrUpdate context d (Diff.idDecl d)
        | Diff.Add _
        | Diff.Delete _ -> []  // nothing to generate for added/deleted declarations
        | Diff.Update(d,df) -> declSameOrUpdate context d df

    /// translates a possibly changed declaration
    // The treatment of unchanged and changed declarations often shares so much code that it is easier
    // to handle both in the same method.
    and declSameOrUpdate (context: Context)(decl: Decl)(dif: Diff.Decl) : Decl list =
        let n = match dif.name with
                | Diff.SameName n -> n
                | Diff.Rename _ -> failwith (unsupported "renamed declaration")
        let p = context.currentDecl.child(n)
        let pO, pN, pT = path p
        let ctxI = context.enter(n)
        match dif with
        | Diff.Class _
        | Diff.ClassConstructor _ -> failwith (unsupported "classes")
        | Diff.Import _
        | Diff.Export _ -> [decl] // TODO check
        | Diff.DUnimplemented -> [decl]
        | Diff.Module (_, msD) ->
            [ Module(n, decls ctxI msD, emptyMeta) ]
        | Diff.TypeDef(_, tvsD, superD, exprD) ->
           if not tvsD.isSame || not superD.isSame || not exprD.isSame then
               failwith(unsupported "change in type declaration: " + p.ToString())
           match decl with
           | TypeDef (_, _, super, _, isNew, _) ->
            // TypeDefs produce methods
            let typeParams, inSpec, outSpec, xtO, xtN = typeDeclHeader (p, decl)
            let xO = localDeclTerm xtO
            let xN = localDeclTerm xtN
            let body =
                if isNew then
                    // new types are new primitive types, so return diagonal relation
                    EEqual(xO, xN)
                else
                    // otherwise, call relation of supertype
                    let _, _, superT = tp super
                    superT (xO, xN)
            [ Method(false, pT.name, typeParams, inSpec, outSpec, Some body, false, true, emptyMeta) ]
            | _ -> failwith("impossible") // Diff.TypeDef must go with YIL.TypeDef

        | Diff.Datatype (_, tvsD, ctrsD, msD) ->
            if not tvsD.isSame then
                failwith (unsupported "change in type parameters: " + p.ToString() )
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

            let mkCase (ctrD: Diff.Elem<YIL.DatatypeConstructor,Diff.DatatypeConstructor>) =
                let ctr = ctrD.yil
                let insO, insN, insT = List.unzip3 (List.map localDecl ctr.ins)
                let argsO = List.map localDeclTerm insO
                let argsN = List.map localDeclTerm insN
                let cn = ctr.name
                let patO = EConstructorApply(pO.child (cn), [], argsO) // type parameters do not matter in a pattern
                let patN = EConstructorApply(pN.child (cn), [], argsN)
                match ctrD with
                // no cases to generate for Add and Delete, but we generate stubs for customization
                | Diff.Add _ ->
                    [{ vars = insN
                       pattern = ETuple([ EWildcard; patN ])
                       body = ECommented("added constructor", EBool false)}]
                | Diff.Delete _ ->
                    [{ vars = insN
                       pattern = ETuple([ patO; EWildcard ])
                       body = ECommented("deleted constructor", EBool false)}]
                | Diff.Update (ctr,ctrU) -> [] // we could generate something here, but it's unclear what
                | Diff.Same ctr ->
                    [{ vars = Utils.listInterleave (insO, insN)
                       pattern = ETuple([ patO; patN ])
                       body = EConj(insT) }]

            let dflt = EBool false
            let xO, xN = localDeclTerm xtO, localDeclTerm xtN
            let tO, tN = localDeclType xtO, localDeclType xtN
            let body = EMatch(ETuple [ xO; xN ], TTuple [ tO; tN ], List.collect mkCase ctrsD.elements, Some dflt)
            let relation = Method(false, pT.name, typeParams, inSpec, outSpec, Some body, false, true, emptyMeta)
            let memberLemmas = decls ctxI msD
            relation :: memberLemmas
        // immutable fields with initializer yield a lemma, mutable fields yield nothing
        | Diff.Field (_, tpD, dfD) ->
           match decl with
           | Field(_, _, dfO, _, isStatic, isMutable, _) when dfO.IsNone || not isStatic || isMutable -> []
           | Field (_, t, _, _, _, _, _) ->
            if not tpD.isSame then
                failwith (unsupported "change in type: " + p.ToString())
            let tO, tN, tT = tp t
            let recO, recN =
                let parentO, parentN, _ = path (context.currentDecl)
                let sr p = StaticReceiver({ path = p; tpargs = [] })
                sr parentO, sr parentN
            let fieldsRelated = tT (EMemberRef(recO, pO, []), EMemberRef(recN, pN, []))
            [ Method(
                  true,
                  pT.name,
                  [],
                  InputSpec([], []),
                  OutputSpec([], [ fieldsRelated ]),
                  None,
                  true,
                  true,
                  emptyMeta
              ) ]
           | _ -> failwith("impossible") // Diff.Field must occur with YIL.Field
        // methods produce lemmas; lemmas produce nothing
        | Diff.Method(_, tvsD, insD, outsD, bdD) ->
           match decl with
           | Method(isLemma=true) -> []
           | Method (_, _, tvs, ins, outs, bodyO, _, isStatic, _) ->
            // for now, we only support a change in the body
            if not tvsD.isSame then
                failwith (unsupported "change in type parameters: " + p.ToString())
            if not insD.isSame then
                failwith (unsupported "change in inputs: " + p.ToString())
            if not outsD.isSame then
                failwith (unsupported "change in outputs: " + p.ToString())
            // as "methods", we only consider pure functions here
            // a more general approach might also generate two-state lemmas for method invocations on class instances
            // (i.e., calling corresponding methods with related arguments on related objects yields related values and
            //   leaves the (possibly changed) objects related)
            //
            // For a static method without specification:
            // method p<u>(x:a,y:u):B = {_} --->
            // lemma  p<uO,uN,vO,vN>(uT:uO*uN->bool, vT:vO*vN->bool, xO:aO, xN:aN, yO:uO, yN:uN))
            //     requires a-related(xO,xN) && uT(yO,yN)
            //     ensures B-related(pO(xO,uO), pN(xN, uN)
            // and accordingly for the general case. If not static, the lemma additionally quantifies over the receivers.
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
                let t = TApply(context.currentDecl, typeargsToTVars parentTvs)
                localDecl (LocalDecl(varname parentDecl.name, t, false))
            let instanceInputs =
                if isStatic then
                    []
                else
                    [ oldInstDecl; newInstDecl ]

            let receiverO, receiverN =
                if isStatic then
                    // ignores the instances above
                    let sr p = StaticReceiver({ path = p; tpargs = [] })
                    sr parentO, sr parentN
                else
                    let objRec ld = ObjectReceiver(localDeclTerm ld)
                    objRec oldInstDecl, objRec newInstDecl
            // the input types and arguments and the conditions that the latter are related
            // parent type parameters and instanceInputs are empty if static
            let tvsO, tvsN, tvsT = List.unzip3 (List.map typearg tvs)
            let typeParams = Utils.listInterleave (parentTvsO @ tvsO, parentTvsN @ tvsN)
            let insO, insN, insT =
                match ins with
                | InputSpec (lds, _) -> List.unzip3 (List.map localDecl lds)
            let inputs =
                instanceInputs
                @ parentTvsT
                @ tvsT @ Utils.listInterleave (insO, insN)

            let inputRequiresO,inputRequiresN,_ =
                ins.conditions |> List.map (fun c -> expr(c)) |> List.unzip3
            let inputsRelated =
                if isStatic then
                    insT
                else
                    instancesRelated :: insT
            let inSpec = InputSpec(inputs, inputRequiresO @ inputRequiresN @ inputsRelated)
            // we don't need the ensures-conditions of the method
            // because they can be proved from the verification of the method
            // but we might add them if that helps
            
            // the outputs and the condition that they're related
            let _, _, outputTypeT =
                match outs with
                | OutputSpec([hd],_) -> tp hd.tp
                | _ -> failwith (unsupported "multiple output declarations")
            let resultO =
                EMethodApply(receiverO, pO, typeargsToTVars tvsO, List.map localDeclTerm insO, true)
            let resultN =
                EMethodApply(receiverN, pN, typeargsToTVars tvsN, List.map localDeclTerm insN, true)
            let outputsRelated = outputTypeT (resultO, resultN)
            let outSpec = OutputSpec([], [ outputsRelated ])
            
            // The body yields the proof of the lemma.
            let proof =
                match bdD with
                | Diff.SameExprO bdO ->
                    // unchanged body: try to generate proof sketch
                    bdO |> Option.bind (fun b -> let _, _, pf = expr b in pf)
                | _ ->
                    // changed body: generate empty proof
                    None

            [ Method(true, pT.name, typeParams, inSpec, outSpec, proof, true, true, emptyMeta) ]
           | _ -> failwith("impossible") // Diff.Method must occur with YIL.Method

    // joint code for type declarations
    and typeDeclHeader(p: Path, d: Decl) = typeDeclHeaderMain(p, d.name, d.tpvars) 
    and typeDeclHeaderMain(p: Path, n:string, tvs: TypeArg list) =
        let pO, pN, pT = path p
        let tvsO, tvsN, tvsT = List.unzip3 (List.map typearg tvs)
        let typeParams = Utils.listInterleave (tvsO, tvsN)
        let oldType = TApply(pO, typeargsToTVars tvsO)
        let newType = TApply(pN, typeargsToTVars tvsN)
        let xO, xN, _ = name (varname n)
        let xtO = LocalDecl(xO, oldType, false)
        let xtN = LocalDecl(xN, newType, false)
        let inputs = tvsT @ [ xtO; xtN ]
        let inSpec = InputSpec(inputs, [])
        let outSpec = outputType(TBool, [])
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
        let xOE = EVar xO
        let xNE = EVar xN
        let bodyXON = body (xOE, xNE)
        match bodyXON with
        | EAnonApply(EVar n, [a;b]) when a = xOE && b = xNE ->
            // this often introduces an eta-expanded variable ---> eta-contract
            EVar n
        | _ -> 
            EFun(
                [ LocalDecl(xO, tO, false)
                  LocalDecl(xN, tN, false) ],
                TBool,
                bodyXON
            )
    /// tp(t) = (o,n,f) such that o/n are the old/new types corresponding to t and f:n->o is the translation function
    and tp (t: Type) : Type * Type * (Expr * Expr -> Expr) =
        match t with
        | TUnit
        | TBool
        | TInt _
        | TNat _
        | TChar 
        | TString _
        | TReal _
        | TBitVector _ -> t, t, diag
        | TVar a ->
            let aO, aN, aT = name a
            TVar aO, TVar aN, (fun (e, f) -> EAnonApply(EVar aT, [ e; f ]))
        | TApply (p, ts) ->
            let pO, pN, pT = path p
            let r = StaticReceiver({ path = pT.parent; tpargs = [] })
            let tsONT = List.map tp ts
            let tsT = List.map (fun (o, n, t) -> abstractRel ("x", o, n, t)) tsONT
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
                    let esT = List.map (fun (i, t) -> t (EProj(x, i), EProj(y, i))) its
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
        | TNullable t ->
            let tO, tN, tT = tp t
            TNullable tO, TNullable tN, (fun e -> EDisj [EEqual(ETuple[fst e;snd e], ETuple([ENull tO; ENull tN])); tT e])
        | TSeq(b,t) ->
            let tO, tN, tT = tpAbstracted("sq", t)
            TSeq(b,tO), TSeq(b,tN), seqRel tO tN tT
        | TSet(b,t) ->
            let tO, tN, tT = tpAbstracted("st", t)
            TSet(b,tO), TSet(b,tN), setRel tO tN tT
        | TMap(b,s, t) ->
            let sO, sN, sT = tpAbstracted("mp", s)
            let tO, tN, tT = tpAbstracted("mp", t)
            TMap(b, sO, tO), TMap(b, sN, tN), mapRel sO sN sT tO tN tT
        | TArray(b,t) ->
            let tO, tN, tT = tpAbstracted("ar", t)
            TArray(b,tO), TArray(b,tN), arrayRel tO tN tT
        | TOption t ->
            let tO, tN, tT = tpAbstracted("opt", t)
            TOption tO, TOption tN, optionRel tO tN tT
        | TUnimplemented -> TUnimplemented, TUnimplemented, (fun _ -> EUnimplemented)
    /// same as tp but with the relation lambda-abstracted
    and tpAbstracted(x: string, t: Type) =
        let tO, tN, tT = tp t
        tO, tN, abstractRel(x, tO, tN, tT)
        

    /// translates expression e:t to the proof that it is in the t-relation
    ///
    /// if |- e:t and tp t = tO, tN, tT, then
    /// post(expr(e,t) = eO,eN,eT where eT is a proof of tT(eO,eN)
    /// Dafny does not have full proof terms and finds proofs automatically.
    /// So it's not clear what can/should return here.
    /// But we probably have to return the instances of the lemmas generated by the methods used in e.
    /// For now, we return None so that we can call the function already.
    and expr (e: Expr) : Expr * Expr * (Expr option) =
      let eO = NameTranslator(true).expr(Context(prog), e)
      let eN = NameTranslator(false).expr(Context(prog), e)
      eO,eN,None
      
    member this.doProg() = decls (Context prog) progD.decls
    
  /// entry point to call the translator on a program
  /// the resulting program consists of 4 parts
  /// Joint.X ---> Old.X
  ///  |            |
  ///  V            V
  /// New.X  ---> Combine.X
  /// where X is the name of a module in the original program.
  /// Modules Joint.X are shared among old and new program. Modules Old.X and New.X occur
  /// in only one of the two (add or delete) or both (update).
  /// This method
  /// - computes the set of declarations in the Joint part
  /// - generates the Combine part.
  /// A subsequent step is expected to copy the old and new program and prefix the names in all toplevel
  /// declarations with either "Joint." or "New.", resp. "Old.".
  let prog (p: Program, pD: Diff.Program) : Program * Path list =
    let ctx = Context(p)
    let pathOf(d: Decl) = ctx.currentDecl.child(d.name)
    let childPaths = List.map pathOf p.decls // toplevel paths of p
    let sameChildren = List.map pathOf pD.decls.getSame  // the unchanged ones among those
    let changedChildren = Utils.listDiff(childPaths, sameChildren) // the changed ones
    let changedClosed = Analysis.dependencyClosure(ctx, p.decls, changedChildren) // dependency closure of the changed ones
    let jointPaths = Utils.listDiff(childPaths, changedClosed) // greatest self-contained set of unchanged declarations
    let tr = Translator(p,pD,jointPaths)
    let combine = {name = p.name; decls = tr.doProg()} // the Combine part
    combine, jointPaths
