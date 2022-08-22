namespace TypeInjections

open System
open TypeInjections.Diff
open TypeInjections.Traverser
open YIL

/// Wrappers for standard Dafny functions that we assume to exist; need to be written and added to yucca
module DafnyFunctions =
    let rb = Path ["Translations"; "RelateBuiltinTypes"]
    let rbRec = StaticReceiver {path=rb; tpargs=[]}
    /// given relation t on o*n, the sequences e: seq<n> and f:seq<n> are related
    /// if they have the same length and are related element-wise
    let seqRel o n t (e,f) = EMethodApply(rbRec, rb.child("seq"), [o;n], [t;e;f], false)
    /// given relation t on o*n, the array e: arr<n> and f:arr<n> are related
    /// if they have the same length and are related element-wise
    let arrayRel o n t (e,f) = EMethodApply(rbRec, rb.child("array"), [o;n], [t;e;f], false)
    /// given relation t on o*n, the sets e: set<n> and f:set<n> are related
    /// if every element of e is related to an element of f and vice versa
    let setRel o n t (e,f) = EMethodApply(rbRec, rb.child("set"), [o;n], [t;e;f], false)
    /// given relations, sT,tT on so*sn and tO*tN, the maps e: map<sO,tO> and f:map<sN,tN> are related
    /// if every pair in e is related a pair in f and vice versa
    let mapRel sO sN sT tO tN tT (e,f) = EMethodApply(rbRec, rb.child("map"), [sO;sN;tO;tN], [sT;tT;e;f], false)

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
    // This is the only place besides functionNames(s) below that uses the literal prefix strings.
    let rec path (p: Path) : Path * Path * Path =
        let prefixRoot (p: Path) (s: string) =
            Path(s :: p.names.Head :: p.names.Tail)
        // joint decls are the same in old and new version
        // the translation declaration is still generated because e.g.,
        // a joint type can be called with non-joint type parameters
        if List.exists (fun (j:Path) -> j.isAncestorOf p) jointDecls then
           (prefixRoot p "Joint", prefixRoot p "Joint", prefixRoot p "Translations")
        else
           (prefixRoot p "Old", prefixRoot p "New", prefixRoot p "Translations")

    /// s ---> s_old, s_new, s
    // This is the only place that uses the literal names.
    and name (s: string) = s+"_O", s+"_N", s
    
    // Function name must be distinct from lemma names. So we prefix all function names with "T_".
    and functionName(s: string) = "TF_" + s

    and lemmaName(s: string) = "TL_" + s
    
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
            //[ relation ] :: memberLemmas
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
                    // new types are new primitive types, so return diagonal relation
                    EEqual(xO, xN)
                else
                    // otherwise, call relation of supertype
                    let _, _, superT = tp super
                    superT (xO, xN)
            [ Method(NonStaticMethod IsFunction, functionName pT.name, typeParams, inSpec, outSpec, Some body, false, true, context.currentMeta()) ]
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
                let buildCase(vs, p1, p2, comment, body) =
                     [{ vars = vs
                        pattern = ETuple([ p1; p2 ])
                        body = ECommented(comment, body) }]

                match elem with
                // no cases to generate for Add and Delete, but we generate stubs for customization
                | Diff.Add _ ->
                    buildCase(insN, EWildcard, patN, "added constructor", EBool false)
                | Diff.Delete _ ->
                    buildCase(insO, patO, EWildcard, "deleted constructor", EBool false)
                | Diff.Same _ ->
                    buildCase(insO @ insN, patO, patN, "unchanged constructor", EConj(insT))
                | Diff.Update _ ->
                    // for updates, we only generate the conditions that the unchanged arguments are related
                    // the relation must be customized in a way that takes the added/deleted arguments into account 
                    buildCase(insO @ insN, patO, patN, "added/deleted constructor arguments", EConj(insT))
            let dflt = EBool false
            let xO, xN = localDeclTerm xtO, localDeclTerm xtN
            let tO, tN = localDeclType xtO, localDeclType xtN
            let body = EMatch(ETuple [ xO; xN ], TTuple [ tO; tN ], List.collect mkCase ctrsD.elements, Some dflt)
            let relation = Method(NonStaticMethod IsFunction,  functionName pT.name, typeParams, inSpec, outSpec, Some body, false, true, emptyMeta)
            let memberLemmas = decls ctxI msD
            relation :: memberLemmas
        // immutable fields with initializer yield a lemma, mutable fields yield nothing
        | Diff.Field (_, tpD, dfD) ->
           match declO with
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
                  NonStaticMethod IsLemma,
                  lemmaName pT.name,
                  [],
                  InputSpec([], []),
                  OutputSpec([], [ fieldsRelated ]),
                  None,
                  true,
                  true,
                  emptyMeta
              ) ]
           | _ -> failwith("impossible") // Diff.Field must occur with YIL.Field
        // Dafny functions produce lemmas; lemmas / Dafny methods produce nothing
        | Diff.Method(_, tvsD, insD, outsD, bdD)  ->
           match declO,declN with
           | Method(methodIs = (NonStaticMethod IsLemma)), _
           | Method(methodIs = (StaticMethod IsLemma)), _
           | Method(methodIs = (NonStaticMethod IsMethod)), _
           | Method(methodIs = (StaticMethod IsMethod)), _ -> []
           | Method (_, _, tvs, ins_o, outs, bodyO, _, isStatic, _),
             Method (_, _, _,   ins_n, _, _, _, _, _) ->
            // we ignore bodyO, i.e., ignore changes in the body
            if not tvsD.isSame then
                failwith (unsupported "change in type parameters: " + p.ToString())
            // we ignore changes in in/output conditions here and only compare declarations
            // in fact, ensures clauses (no matter if changed) are ignored entirely
            if not (insD.decls.getUpdate().IsEmpty) then
                failwith (unsupported "update to individual inputs: " + p.ToString())
            if not outsD.decls.isSame then
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
            // old inputs and new inputs
            let insO, _, _ = List.unzip3 (List.map localDecl ins_o.decls)
            let _, insN, _ = List.unzip3 (List.map localDecl ins_n.decls)
            // assumptions that the inputs occuring in both old and new are related
            let _,_, insT = List.unzip3 (List.map localDecl (insD.decls.getSame()))
            let inputs =
                instanceInputs
                @ parentTvsT
                @ tvsT @ insO @ insN

            // old requires clauses applied to old arguments
            let inputRequiresO,_,_ =
                ins_o.conditions |> List.map (fun c -> expr(c)) |> List.unzip3
            // new requires clauses applied to new arguments
            let _,inputRequiresN,_ =
                ins_n.conditions |> List.map (fun c -> expr(c)) |> List.unzip3
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
                | Some ot -> ot (resultO, resultN)
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
                    None

            [ Method(NonStaticMethod IsLemma, pT.name, typeParams, inSpec, outSpec, proof, true, true, emptyMeta) ]
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
            let tps = tpDs.getSame()
            let lds = ldDs.getSame()
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
            let tsONT= List.map tp ts
            let tsT = List.map (fun (o, n, t) -> abstractRel ("x", o, n, t)) tsONT
            let tsO, tsN, _ = List.unzip3 tsONT
            let tsON = Utils.listInterleave (tsO, tsN)
            TApply(pO, tsO), TApply(pN, tsN), (fun (x, y) -> EMethodApply(r, pT.transformLast(functionName pT.name), tsON, tsT @ [ x; y ], false))
        | TApplyPrimitive (p, t) ->
            let pO, pN, pT = path p
            let r = StaticReceiver({ path = pT.parent; tpargs = [] })
            let tO, tN, tONT = tp t
            let primitiveTO = TApplyPrimitive(pO, tO)
            let primitiveTN = TApplyPrimitive(pN, tN)
            // TApplyPrimitive(...) is really just a transparent wrapper type here designed to give us
            // access to the fully qualified path of a type, so tONT operating on tO and tN should still
            // be a valid translation function here.
            TApplyPrimitive(pO, tO), TApplyPrimitive(pN, tN), tONT
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
            let outputTypeO, outputTypeN, outputTypeRelation = tp u
            let inputDecls = Utils.listInterleave (ldsO, ldsN)
            let inputsO = List.map localDeclTerm ldsO
            let inputsN = List.map localDeclTerm ldsN
            let inputsRelated = EConj(ldsT)

            let funsRelated (o, n) =
                let outputO = EAnonApply(o, inputsO)
                let outputN = EAnonApply(n, inputsN)
                let outputRelated = outputTypeRelation (outputO, outputN)
                EQuant(Forall, inputDecls, Some(inputsRelated), outputRelated)

            TFun(inputTypesO, outputTypeO), TFun(inputTypesN, outputTypeN), funsRelated
        | TObject ->
            // see the treatment of class declarations
            TObject, TObject, EEqual
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
      let eO = NameTranslator(true).expr(ctx, e)
      let eN = NameTranslator(false).expr(ctx, e)
      eO,eN,None
    
    // alternate constructor for diffing two programs at once with module-level granularity
    new(prog: Program, progD: Diff.Program, jointDecls: Path list) =
        Translator(Context(prog), progD.decls, jointDecls)
        
    member this.doTranslate() = decls ctx declsD
  
  /// entry point to call translator on a module
  /// assumes the module is at the program toplevel
  /// dependency analysis is done at the intermodule level, with granularity of every decl child of the module.
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
      let inputOk (nameO: string) (nameD: Name) =
          match nameD with
          | SameName s -> nameO.Equals(s)
          | Rename(o, n) -> nameO.Equals(o)
      match m, pD with
      | YIL.Module _ as m, Diff.Module (nameD, declD) when (inputOk m.name nameD)->
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
          let tr = Translator(ctx, declD, jointPaths)
          tr.doTranslate(), jointPaths
      | _ -> failwith "declaration to be translated is not a module"
  
 


