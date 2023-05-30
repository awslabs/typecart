namespace TypeInjections

open System
open YIL

/// Wrappers for standard Dafny functions that we assume to exist; need to be written and added to yucca
module DafnyFunctions =
    let rcv p = StaticReceiver {path=p; tpargs=[]}
    let fb = Path ["Translations"; "MapBuiltinTypes"]
    let rcvFunc = rcv fb
    let utils = rcv (Path ["Translations"; "Utils"])
    /// given translation t: o -> n,
    /// return element-wise translation: seq<o> -> seq<n>
    let seqRel o n t e = EMethodApply(rcvFunc, fb.child("Seq"), [o;n], [t;e], false)
    /// given translation t: o -> n,
    /// return element-wise translation: arr<o> -> arr<n>
    let arrayRel o n t e = EMethodApply(rcvFunc, fb.child("Array"), [o;n], [t;e], false)
    /// given translation t: o -> n,
    /// return element-wise translation: set<o> -> set<n>
    let setRel o n t e = EMethodApply(rcvFunc, fb.child("Set"), [o;n], [t;e], false)
    /// given translations sT1: sO -> sN, sT2: sN -> sO, tT1: tO -> tN, tT2: tN -> tO,
    /// return translation: map<sO, tO> -> map<sN, tN> for each element e in sN with a preimage in sT1
    let mapRel sO sN (sT1, sT2) tO tN (tT1, tT2) e = EMethodApply(rcvFunc, fb.child("Map"), [sO;sN;tO;tN], [sT1;sT2;tT1;e], false)
    /// ???()
    let missingTerm = EMethodApply(utils, fb.child("???"), [], [], false)
    
open DafnyFunctions

// variable naming conventions:
//  xD: diff between two x's
//  xT: translation of x

/// takes a diff between two YIL objects and returns the translation declarations/objects for it
module Translation =
  let unsupported s = "unsupported: " + s
  
  /// translates a program, encapsulates global data/state for use during translation
  type Translator(ctx: Context, declsD: Diff.DeclList, jointDecls: Path list, relational: bool) =    
    /// old, new, and translations path for a path
    // This is the only place that uses the literal prefix strings.
    let rec path (p: Path) : Path * Path * Path =
        // joint decls are the same in old and new version
        // the translation declaration is still generated because e.g.,
        // a joint type can be called with non-joint type parameters
        if List.exists (fun (j:Path) -> j.isAncestorOf p) jointDecls then
           (p.prefix "Joint", p.prefix "Joint", p.prefix "Translations")
        else
           (p.prefix "Old", p.prefix "New", p)

    /// s ---> s_old, s_new, s
    // This is the only place that uses the literal names.
    and name (s: string) = s+"_O", s+"_N", s
    
    /// a --->  a_old, a_new, a: a_old * a_new -> bool
    and typearg (a: TypeArg) : TypeArg * TypeArg * LocalDecl =
        let v = snd a
        let aO, aN, aT = name (fst a)
        (aO,v), (aN,v), LocalDecl(aT, TFun([TVar aO;TVar aN], TBool), false)

    /// suggests a name for a variable of the type defined by a declaration name
    and varname (n:string) = n.Chars(0).ToString()
      
    /// translates paths and type/expr variables to old or new variant
    // empty context must be passed so that traversal context tracks local bindings
    and NameTranslator(old: bool) =
         {new Traverser.Identity() with
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
                    let nO,nN,_ = typearg (plainTypeArg n)
                    TVar(if old then fst nO else fst nN)
                | _ -> this.tpDefault(ctx, t)
        }
    
    /// convenience for iteration over a list of declarations
    and decls (context: Context) (dsD: Diff.List<Decl, Diff.Decl>) =
        List.collect (decl context) dsD.elements

    /// translates one declaration
    and decl (context: Context) (dD: Diff.Elem<Decl, Diff.Decl>) : Decl list =
        match dD with
        | Diff.Same d -> declSameOrUpdate context (d,d) (Diff.idDecl d)
        | Diff.Add _
        | Diff.Delete _ -> []  // nothing to generate for added/deleted declarations
        | Diff.Update(d,n,df) -> declSameOrUpdate context (d,n) df

    /// translates a possibly changed declaration
    // The treatment of unchanged and changed declarations often shares so much code that it is easier
    // to handle both in the same method.
    and declSameOrUpdate (context: Context)(declO: Decl, declN: Decl)(dif: Diff.Decl) : Decl list =
        let n = match dif.name with
                | Diff.SameName n -> n
                | Diff.Rename _ -> failwith (unsupported "renamed declaration")
        let p = context.currentDecl.child(n)
        let pO, pN, pT = path p
        let ctxI = context.enter(n)
        match dif with
        | Diff.Class(_,_,_,msD) ->
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
        | Diff.Import _
        | Diff.Export _ -> [declO] // TODO check what to do here if anything
        | Diff.DUnimplemented -> [declO]
        | Diff.Module (_, msD) ->
            [ Module(n, decls ctxI msD, context.currentMeta()) ]
        | Diff.TypeDef(_, tvsD, superD, exprD) ->
           if not tvsD.isSame || not superD.isSame || not exprD.isSame then
               failwith(unsupported "change in type declaration: " + p.ToString())
           match declO with
           | TypeDef (_, _, super, _, isNew, _) ->
            // TypeDefs produce methods
            let typeParams, inSpec, outSpec, xtO, xtN = typeDeclHeader (p, declO)
            let xO = localDeclTerm xtO
            let xN = localDeclTerm xtN
            let body =
              if isNew then
                // new types are new primitive types, so return identity map
                xO
              else
                // otherwise, call function of supertype
                let _, _, superT = tp super
                (fst superT) xO
                   
            [ Method(IsFunction, pT.name, typeParams, inSpec, outSpec, [], [], [], Some body, false, true, context.currentMeta()) ]
            | _ -> failwith("impossible") // Diff.TypeDef must go with YIL.TypeDef

        | Diff.Datatype (_, tvsD, ctrsD, msD) ->
            if not tvsD.isSame then
                failwith (unsupported "change in type parameters: " + p.ToString() )
            let tvs = tvsD.getSame()
            // datatype p.name<u,v> = con1(a,u) | con2(b,v) --->
            // datatype pO<uO,vO> = con1(aO,uO) | con2(bO,vO)
            // datatype pN<uN,vN> = con1(aN,uN) | con2(bN,vN)
            // function pT<uO,uN,vO,vN>(uT:uO*uN->bool, vT:vO*vN->bool, xO:pO(uO,vO), xN:pN(uN,vN)) = match xO,xN
            //   | con1(x1,x2), con1(y1,y2) => aT(x1,y1) && uT(x2,y2)
            //   | con2(x1,x2), con2(y1,y2) => bT(x1,y1) && vT(x2,y2)
            //   | _ -> false
            // and accordingly for the general case.
            let typeParams, inSpec, outSpec, xtO, xtN = typeDeclHeaderMain (p, n, tvs)

            let mkCase (elem: Diff.Elem<YIL.DatatypeConstructor,Diff.DatatypeConstructor>) =
                // to share code between the cases, we interpret the change as an update 
                // old and new constructor and the diff
                let ctrO,ctrN,ctrD =
                    match elem with
                    | Diff.Update(o,n,d) -> o,n,d
                    | _ ->
                        // if not an Update, we use default values that are only used partially below
                        elem.yil, elem.yil, Diff.idConstructor elem.yil
                let insO, _, _ = List.unzip3 (List.map localDecl ctrO.ins)
                let _, insN, _ = List.unzip3 (List.map localDecl ctrN.ins)
                let _, _, insT =
                    if not (ctrD.ins().getUpdate().IsEmpty) then
                        failwith (unsupported "update to datatype constructor argument")
                    List.unzip3 (List.map localDecl (ctrD.ins().getSame()))
                let argsO = List.map localDeclTerm insO
                let argsN = List.map localDeclTerm insN
                let patO = EConstructorApply(pO.child (ctrO.name), [], argsO) // type parameters do not matter in a pattern
                let patN = EConstructorApply(pN.child (ctrN.name), [], argsN)
                // to share code between two cases below
                // "case (p1,p2) -> body // comment" where vs_i are the variables in p_i
                let buildCase(vs1, vs2, p1, p2, comment, body) =
                     [{ vars = if relational then vs1 @ vs2 else vs1
                        pattern = if relational then ETuple([ p1; p2 ]) else p1
                        body = ECommented(comment, body) }]
                match elem with
                // no cases to generate for Add and Delete, but we generate stubs for customization
                | Diff.Add _ ->
                    if relational then
                       // case (_,n) -> false
                       buildCase([], insN, EWildcard, patN, "added constructor", EBool false)
                    else
                       // nothing to do
                       []
                | Diff.Delete _ ->
                    if relational then
                       // case (o,_) -> false
                       buildCase(insO, [], patO, EWildcard, "deleted constructor", EBool false)
                    else
                       // case o -> ???
                       buildCase(insO, [], patO, EWildcard, "deleted constructor", missingTerm) 
                | Diff.Same _ ->
                    // if relational then
                       // case (o,n) -> arguments of o,n related
                       // buildCase(insO, insN, patO, patN, "unchanged constructor", EConj(insT))
                    // else
                       // TODO this case is unfinished
                       buildCase(insO, [], patO, EWildcard, "unchanged constructor", patN)
                | Diff.Update _ ->
                    // if relational then
                        // for updates, we only generate the conditions that the unchanged arguments are related
                        // the relation must be customized in a way that takes the added/deleted arguments into account 
                        // buildCase(insO, insN, patO, patN, "added/deleted constructor arguments", EConj(insT))
                    // else
                        // TODO this case is unfinished
                        buildCase(insO, [], patO, EWildcard, "added/deleted constructor arguments", patN)
            let dflt = if relational then Some (EBool false) else None
            let xO, xN = localDeclTerm xtO, localDeclTerm xtN
            let tO, tN = localDeclType xtO, localDeclType xtN
            let scrutinee,scrutineeTp =
                if relational then
                   ETuple [ xO; xN ],  TTuple [ tO; tN ]
                else
                   xO, tO
            let body = EMatch(scrutinee,scrutineeTp, List.collect mkCase ctrsD.elements, dflt)
            let relation = Method(IsFunction, pT.name, typeParams, inSpec, outSpec, [], [], [], Some body, false, true, emptyMeta)
            let memberLemmas = decls ctxI msD
            // wrap all declarations generated by members into a module to avoid name clashes
            // TODO: all paths to a lemma generated by a datatype function must insert "_Lemma"
            let decls = [relation; Module(n+"_Lemmas", memberLemmas, emptyMeta)]
            decls
        // immutable fields with initializer yield a lemma, mutable fields yield nothing
        | Diff.Field (_, tpD, dfD) ->
           match declO with
           | Field(_, _, dfO, _, isStatic, isMutable, _) when dfO.IsNone || not isStatic || isMutable -> []
           | Field (_, t, _, _, _, _, _) ->
            if not tpD.isSame then
                failwith (unsupported "change in type: " + p.ToString())
            let tO, tN, tT = tp t
            let tT1, tT2 = tT
            let recO, recN =
                let parentO, parentN, _ = path (context.currentDecl)
                let sr p = StaticReceiver({ path = p; tpargs = [] })
                sr parentO, sr parentN
            let fieldsRelated = EEqual(tT1 (EMemberRef(recO, pO, [])), EMemberRef(recN, pN, []))
            [ Method(
                  IsLemma,
                  pT.name,
                  [],
                  InputSpec([], []),
                  OutputSpec([], [ fieldsRelated ]),
                  [], [], [],
                  Some (EBlock []),
                  true,
                  true,
                  emptyMeta
              ) ]
           | _ -> failwith("impossible") // Diff.Field must occur with YIL.Field
        // Dafny functions produce lemmas; lemmas / Dafny methods produce nothing
        | Diff.Method(_, tvsD, insD, outsD, bdD)  ->
           match declO,declN with
           | Method(methodType = IsLemma), _
           | Method(methodType = IsMethod), _ -> []
           | Method (_, _, tvs, ins_o, outs, modifiesO, readsO, decreasesO, bodyO, _, isStatic, _),
             Method (_, _, _,   ins_n, _, modifiesN, readsN, decreasesN, _, _, _, _) ->
            // we ignore bodyO, i.e., ignore changes in the body
            if not tvsD.isSame then
                failwith (unsupported "change in type parameters: " + p.ToString())
            // we ignore changes in in/output conditions here and only compare declarations
            // in fact, ensures clauses (no matter if changed) are ignored entirely
            if not (insD.decls.getUpdate().IsEmpty) then
                failwith (unsupported "update to individual inputs: " + p.ToString())
            if not outsD.decls.isSame then
                failwith (unsupported "change in outputs: " + p.ToString())
            // if modifies, reads, decreases clauses change, throw an error
            // TODO here
            // as "methods", we only consider pure functions here
            // a more general approach might also generate two-state lemmas for method invocations on class instances
            // (i.e., calling corresponding methods with related arguments on related objects yields related values and
            //   leaves the (possibly changed) objects related)
            //
            // For a static method without specification:
            // method p<u,v>(x:a,y:u):B = {_} --->
            // lemma  p<uO,uN,vO,vN>(uT:uO*uN->bool, vT:vO*vN->bool, xO:aO, xN:aN, yO:uO, yN:uN))
            //     requires a-related(xO,xN) && uT(yO,yN)
            //     ensures B-related(pO(xO,uO), pN(xN, uN)
            // and accordingly for the general case. If not static, the lemma additionally quantifies over the receivers.
            let parentDecl = context.lookupCurrent()
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
                if isStatic then [] else [ oldInstDecl; newInstDecl ]
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
            // old inputs and new inputs
            let insO, _, _ = List.unzip3 (List.map localDecl ins_o.decls)
            let _, insN, _ = List.unzip3 (List.map localDecl ins_n.decls)
            // assumptions that the inputs occuring in both old and new are related
            let _,_, insT = List.unzip3 (List.map localDecl (insD.decls.getSame()))
            let inputs = instanceInputs @ parentTvsT @ tvsT @ insO @ insN
            // old requires clauses applied to old arguments
            let inputRequiresO,_,_ =
                ins_o.conditions |> List.map (fun c -> expr(c)) |> List.unzip3
            // new requires clauses applied to new arguments
            let _,inputRequiresN,_ =
                ins_n.conditions |> List.map (fun c -> expr(c)) |> List.unzip3
            let inputsTranslations =
                if isStatic then insT else instancesRelated :: insT
            // inputsTranslations is (f1(old), f2(new))
            // backward compatibility: f1(old) == new
            let inputsRelated = List.map (fun ((f1, f2), inN:LocalDecl) -> EEqual(f1, EVar(inN.name)))
                                    (List.zip inputsTranslations insN)
            
            let inSpec = InputSpec(inputs, inputRequiresO @ inputRequiresN @ inputsRelated)
            // we don't need the ensures-conditions of the method
            // because they can be proved from the verification of the method
            // but we might add them if that helps
            
            // the outputs and the condition that they're related
            let outputTypeT =
                match outs with
                | OutputSpec([],_) -> None
                | OutputSpec([hd],_) ->
                    let _,_,ot = tp hd.tp
                    Some ot
                | _ -> failwith (unsupported "multiple output declarations")
            let resultO =
                EMethodApply(receiverO, pO, typeargsToTVars tvsO, List.map localDeclTerm insO, true)
            let resultN =
                EMethodApply(receiverN, pN, typeargsToTVars tvsN, List.map localDeclTerm insN, true)
            let outputsRelated =
                match outputTypeT with
                | Some ot -> EEqual((fst ot) resultO, resultN)
                | None -> EBool true
            // in general for mutable classes, we'd also have to return that the receivers remain related
            // but that is redundant due to our highly restricted treatment of classes
            let outSpec = OutputSpec([], [ outputsRelated ])
            
            // The body yields the proof of the lemma.
            let proof =
                match bdD with
                | Diff.SameExprO bdO ->
                    // unchanged body: try to generate proof sketch
                    bdO |> Option.bind (fun b -> let _, _, pf = expr b in pf)
                | _ ->
                    // changed body: generate empty proof
                    Some (EBlock [])

            [ Method(IsLemma, pT.name, typeParams, inSpec, outSpec, [], [], [], proof, true, true, emptyMeta) ]
           | _ -> failwith("impossible") // Diff.Method must occur with YIL.Method

    /// joint code for type declarations
    and typeDeclHeader(p: Path, d: Decl) = typeDeclHeaderMain(p, d.name, d.tpvars) 
    /// in: declaration path/name and type arguments
    /// out: header of relation:
    ///   * path
    ///   * type arguments
    ///   * input spec: relations/functions for the type arguments, elements of old type, and (if relational) new type
    ///   * output spec: if relational bool, else new type
    ///   * declaration for variable of old type
    ///   * declaration for variable of new type
    and typeDeclHeaderMain(p: Path, n:string, tvs: TypeArg list) =
        let pO, pN, pT = path p
        let tvsO, tvsN, tvsT = List.unzip3 (List.map typearg tvs)
        let typeParams = Utils.listInterleave (tvsO, tvsN)
        let oldType = TApply(pO, typeargsToTVars tvsO)
        let newType = TApply(pN, typeargsToTVars tvsN)
        let xO, xN, _ = name (varname n)
        let xtO = LocalDecl(xO, oldType, false)
        let xtN = LocalDecl(xN, newType, false)
        let inputs = if relational then tvsT @ [ xtO; xtN ] else  tvsT @ [xtO] 
        let inSpec = InputSpec(inputs, [])
        let outType = if relational then TBool else newType
        let outSpec = outputType(outType, [])
        typeParams, inSpec, outSpec, xtO, xtN    

    /// translates a context, e.g., the arguments of a polymorphic method
    /// Ideally, we would translate type and term variables individually and collect the results.
    /// But type variables give rise to both type and term variables,
    /// and term variables give rise to both term variables and preconditions,
    /// which cannot alternate in a Dafny context.
    /// Therefore, we translate them at once using multiple outputs.
    and context (tpDs: Diff.TypeArgList, ldDs: Diff.LocalDeclList) : TypeArg list * LocalDecl list * (Condition * Condition) list =
        if tpDs.isSame && ldDs.isSame then
            let tps = tpDs.getSame()
            let lds = ldDs.getSame()
            let tpsO, tpsN, tpsT = List.unzip3 (List.map typearg tps)
            let ldsO, ldsN, ldsT = List.unzip3 (List.map localDecl lds)
            Utils.listInterleave (tpsO, tpsN), tpsT @ Utils.listInterleave (ldsO, ldsN), ldsT
        else
            failwith (unsupported "change in type/term arguments")

    /// x:a --->
    /// x_old: a_old, x_new: a_new, (translate(x_old), translate(x_new))
    and localDecl (ld: LocalDecl) : LocalDecl * LocalDecl * (Condition * Condition) =
        let nO, nN, nT = name ld.name
        let tO, tN, tT = tp ld.tp
        let g = ld.ghost
        LocalDecl(nO, tO, g), LocalDecl(nN, tN, g), ((fst tT) (EVar nO), (snd tT) (EVar nN))

    and listOfFuncToFuncOfList (l: (Expr -> Expr) List) = (fun x -> List.map (fun (a, b) -> a b) (List.zip l x))
    /// diagonal relation
    and diag (x: Expr, y: Expr) = EEqual(x, y)
    /// reduction to avoid synthesizing reducible terms
    and reduce(e: Expr) = Traverser.reduce(ctx, e)
    /// convenience for building a lambda-abstraction
    and abstractRel (x: string, tO: Type, tN: Type, body: Expr -> Expr) =
        let xO, _, _ = name (x)
        let xOE = EVar xO
        let bodyXOE = body xOE
        let abs = EFun(
                    [ LocalDecl(xO, tO, false) ],
                    tN,
                    bodyXOE
                  )
        reduce abs // reduce eta-contracts
    /// tp(t) = (o,n,(T1,T2)) such that o/n are the old/new types corresponding to t, T1: o->n and T2: n->o are the
    /// translation functions for t.
    and tp (t: Type) : Type * Type * ((Expr -> Expr) * (Expr -> Expr)) =
        match t with
        | TUnit
        | TBool
        | TInt _
        | TNat _
        | TChar 
        | TString _
        | TReal _
        | TBitVector _
        | TObject ->
            t, t, (id, id)
        | TVar a ->
            let aO, aN, aT = name a
            // apply the function of the type variable to the old/new value
            TVar aO, TVar aN, ((fun e -> EAnonApply(EVar aT, [e])), (fun e -> EAnonApply(EVar aT, [e])))
        | TApply (p, ts) ->
            let pO, pN, pT = path p
            let r = StaticReceiver({ path = pT.parent; tpargs = [] })
            let tsONT = List.map tp ts
            let tsT = List.map (fun (o, n, (t1, t2)) -> (abstractRel ("x", o, n, t1), abstractRel ("x", o, n, t2))) tsONT
            let tsT1, tsT2 = List.unzip tsT
            let tsO, tsN, _ = List.unzip3 tsONT
            let tsON = Utils.listInterleave (tsO, tsN)
            TApply(pO, tsO), TApply(pN, tsN), ((fun x -> EMethodApply(r, pT, tsO, tsT1@[x], false)), (fun x -> EMethodApply(r, pT, tsN, tsT2@[x], false)))
        | TTuple ts ->
            // element-wise translations on tuples
            let tsO, tsN, tsT = List.unzip3 (List.map tp ts)
            let its = List.indexed tsT
            let T1 x =
                let esT1 = its |> List.map (fun (i, (t1, _)) -> t1 (reduce(EProj(x, i)))) // reduce eliminates projections from tuples
                ETuple(esT1) // tuple of component mappings
            let T2 x =
                let esT2 = its |> List.map (fun (i, (_, t2)) -> t2 (reduce(EProj(x, i)))) // reduce eliminates projections from tuples
                ETuple(esT2) // tuple of component mappings
            TTuple tsO, TTuple tsN, (T1, T2)
        | TFun (ts, u) ->
            // translate functions
            // x1:t1, ..., xn:tn
            let lds =
                List.indexed ts
                |> List.map (fun (i, t) -> LocalDecl("x" + (i + 1).ToString(), t, false))
            // ldsO = x1O:t1O, ..., xnO:tnO
            // ldsN = x1N:t1N, ..., xnN:tnN
            // ldsT = t1-translations(x1O,x1N), ..., tN-translations(xnO,xnN)
            let ldsO, ldsN, ldsT = List.unzip3 (List.map localDecl lds)
            let ldsT1, ldsT2 = List.unzip ldsT  // unused... is ldsT1 the same as T1 inputsO?
            let inputTypesO = List.map localDeclType ldsO
            let inputTypesN = List.map localDeclType ldsN
            let inputsO = List.map localDeclTerm ldsO
            let inputsN = List.map localDeclTerm ldsN
            // input type translation functions
            let tsO, tsN, tsT = List.unzip3 (List.map tp ts)
            let its = List.indexed tsT
            let T1 x = List.map (fun ((t1, _), x) -> t1 x) (List.zip tsT x)
            let T2 x = List.map (fun ((_, t2), x) -> t2 x) (List.zip tsT x)
            // output type translation functions
            let outputTypeO, outputTypeN, (outputT1, outputT2) = tp u
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
        | TNullable t ->
            let tO, tN, tT = tp t
            let tT1 = fun x -> EIf(EEqual(x,ENull tO), ENull tN, Some ((fst tT) x))
            let tT2 = fun x -> EIf(EEqual(x,ENull tN), ENull tO, Some ((snd tT) x))
            TNullable tO, TNullable tN, (tT1, tT2)
        | TSeq(b,t) ->
            let tO, tN, tT = tpAbstracted("sq", t)
            TSeq(b,tO), TSeq(b,tN), (seqRel tO tN (fst tT), seqRel tN tO (snd tT))
        | TSet(b,t) ->
            let tO, tN, tT = tpAbstracted("st", t)
            TSet(b,tO), TSet(b,tN), (setRel tO tN (fst tT), setRel tN tO (snd tT))
        | TMap(b,s, t) ->
            let sO, sN, sT = tpAbstracted("mp", s)
            let tO, tN, tT = tpAbstracted("mp", t)
            TMap(b, sO, tO), TMap(b, sN, tN), ((mapRel sO sN sT tO tN tT), (mapRel sN sO (snd sT, fst sT) tN tO (snd tT, fst tT)))
        | TArray(b,t) ->
            let tO, tN, tT = tpAbstracted("ar", t)
            TArray(b,tO), TArray(b,tN), (arrayRel tO tN (fst tT), arrayRel tN tO (snd tT))
        | TUnimplemented -> TUnimplemented, TUnimplemented, ((fun _ -> EUnimplemented), (fun _ -> EUnimplemented))
    /// same as tp but with the relation lambda-abstracted
    and tpAbstracted(x: string, t: Type) =
        let tO, tN, tT = tp t
        tO, tN, (abstractRel(x, tO, tN, (fst tT)), abstractRel(x, tN, tO, (snd tT)))
        

    /// translates expression e:t to the proof that it is in the t-relation
    ///
    /// if |- e:t and tp t = tO, tN, tT, then
    /// expr(e,t) = eO,eN,eT where eT is a proof of tT(eO,eN)
    /// Dafny does not have full proof terms and finds proofs automatically.
    /// So it's not clear what can/should return here.
    /// But we probably have to return the instances of the lemmas generated by the methods used in e.
    /// For now, we return None so that we can call the function already.
    and expr (e: Expr) : Expr * Expr * (Expr option) =
      let eO = NameTranslator(true).expr(ctx, e)
      let eN = NameTranslator(false).expr(ctx, e)
      eO,eN,None

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
  let translateModule(ctx: Context,  m: Decl, pD: Diff.Decl)  =
      let ctx = ctx.enter(m.name) // enter decl of m
      let inputOk (nameO: string) (nameD: Diff.Name) =
          match nameD with
          | Diff.SameName s -> nameO = s
          | Diff.Rename(o, n) -> nameO = o
      match m, pD with
      | Module _ as m, Diff.Module (nameD, declD) when (inputOk m.name nameD)->
          let pathOf = fun (decl: Decl) -> Path [ m.name; decl.name ]
          let childPaths = List.map pathOf m.children
          let sameChildren = List.map pathOf (declD.getSame())
          let changedChildren = Utils.listDiff(childPaths, sameChildren)
          let changedClosed = Analysis.dependencyClosure(ctx, m.children, changedChildren)
          let jointPaths = Utils.listDiff(childPaths, changedClosed)
          Console.WriteLine($" ***** DEPENDENCY CLOSURE FOR {m.name} *****")
          List.iter (fun (Path x) -> Console.WriteLine(String.concat ", " x)) changedClosed
          Console.WriteLine($" ***** JOINT PATHS FOR {m.name} *****")          
          List.iter (fun (p: Path) -> Console.WriteLine((p.ToString()))) jointPaths
          Console.WriteLine($" ***** JOINT PATHS FOR {m.name} END *****")
          let tr = Translator(ctx, declD, jointPaths, false)
          tr.doTranslate(), jointPaths
      | _ -> failwith "declaration to be translated is not a module"
  
  /// prints a list of paths
  let printPaths(kind: string, ps: Path list) =
      Console.WriteLine("********* " + kind + " *****")
      List.iter (fun x -> Console.WriteLine(x.ToString())) ps
      Console.WriteLine("***** END " + kind + " *****")

  /// entry point for translating a program
  let prog (p: Program, newName: string, pD: Diff.Program) : Program * Path list =
    let ctx = Context(p)
    let pathOf(d: Decl) = ctx.currentDecl.child(d.name)
    let childPaths = List.map pathOf p.decls // toplevel paths of p
    let sameChildren = List.map pathOf (pD.decls.getSame())  // the unchanged ones among those
    let changedChildren = Utils.listDiff(childPaths, sameChildren) // the changed ones
    let changedClosed = Analysis.dependencyClosure(ctx, p.decls, changedChildren) // dependency closure of the changed ones
    let jointPaths = Utils.listDiff(childPaths, changedClosed) // greatest self-contained set of unchanged declarations
    printPaths("unchanged", sameChildren)
    printPaths("changed", changedChildren)
    printPaths("dependency closure of changed", changedClosed)
    printPaths("joint", jointPaths)
    let tr = Translator(Context(p), pD.decls, jointPaths, false)
    let translations = {name = newName; decls = tr.doTranslate(); meta = emptyMeta}
    translations, jointPaths


