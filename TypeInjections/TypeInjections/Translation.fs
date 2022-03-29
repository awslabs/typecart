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

// variable naming conventions:
//  xD: diff between two x's
//  xT: translation of x

/// takes a diff between two YIL objects and returns the translation declarations/objects for it
module Translation =
    open DafnyFunctions
    
    let unsupported s = "unsupported: " + s
    
    let rec prog(pD: Diff.Program): Program =
       match pD.decls with
       | Diff.SameList l ->
          {name="Combine"; decls = l}
       | Diff.UpdateList l ->
          {name="Combine";
           decls = List.collect decl l}
    
    and decl(dD: Diff.Elem<Decl,Diff.Decl>): Decl list =
       match dD with
       | Diff.Same d -> declSame d
       | _ -> failwith (unsupported "change in declaration")
    
    // TODO
    and declSame(d: Decl): Decl list =
       match d with
       | Module _ -> []
       | Class _ -> failwith (unsupported "classes")
       | Datatype _ -> []
       | _ -> []
    
    /// translates a context, e.g., the arguments of a polymorphic method
    /// Ideally, we would translate type and term variables individually and collect the results.
    /// But type variables give rise to both type and term variables,
    /// and term variables give rise to both term variables and preconditions,
    /// which cannot alternate in a Dafny context.
    /// Therefore, we translate them at once using multiple outputs.
    and context(tpDs: Diff.TypeArgList, ldDs: Diff.LocalDeclList):
                TypeArg list * LocalDecl list * Condition list =
       match tpDs, ldDs with
       | Diff.SameList tps, Diff.SameList lds ->
         let tpsT, tpldsT = List.unzip (List.map typearg tps)
         let ldsT,ldconsT = List.unzip (List.map localDecl lds)
         let C l = List.concat l
         (C tpsT), (C tpldsT) @ (C ldsT), (C ldconsT)
       | _ -> failwith (unsupported "change in type/term arguments")
    
    /// old, new, and combine path for a path
    // This is the only place that uses the literal prefix strings.
    and path(p: Path): Path*Path*Path =
       let prefixRoot(p: Path)(s: string) = Path((s + "." + p.names.Head)::p.names.Tail)
       (prefixRoot p "Old", prefixRoot p "New", prefixRoot p "Combine")
   
    /// s ---> s_old, s_new, s
    // This is the only place that uses the literal names.
    and name(s: string) = s+"_old", s+"_new", s
    
    /// a --->  a_old, a_new, a: a_old -> a_new
    and typearg(a: TypeArg): TypeArg list * LocalDecl list =
       let aO,aN,aT = name a
       [aO; aN], [LocalDecl(aT,TFun([TVar aO], TVar aN),false)]
    
    /// ld ---> ld
    // alternatively, produce old/new variables and a precondition that one is mapped to the other
    // x:a ---> x_old: a_old, x_new: a_new, requires a(x_old)=x_new
    and localDecl(ld: LocalDecl): LocalDecl list * Condition list =
        let nO,nN,nT = name ld.name
        let tO,tN,tT = tp ld.tp
        let g = ld.ghost
        [LocalDecl(nO,tO,g); LocalDecl(nN,tN,g)], [EEqual(tT (EVar nO), EVar nN)]
    
    /// tp(t) = (o,n,f) such that o/n are the old/new types corresponding to t and f:n->o is the translation function
    and tp(t: Type): Type*Type*(Expr->Expr) =
      match t with
      | TUnit
      | TBool
      | TInt
      | TNat
      | TChar
      | TString
      | TReal
      | TBitVector _ -> t,t,id
      | TVar a ->
         let aO,aN,aT = name a
         TVar aO, TVar aN, fun e -> EAnonApply(EVar aT, [e])
      | TApply(p,ts) ->
         let pO,pN,pT = path p
         let r = StaticReceiver({path=pT.parent; tpargs=[]})
         let tONT = List.map tp ts
         let tsTAbs = List.map (fun (O,N,T) -> lambda("x", O, N, T)) tONT
         let tsO,tsN,_ = List.unzip3 tONT
         let tsON = List.collect (fun (x,y) -> [x;y]) (List.zip tsO tsN)
         TApply(pO,tsO), TApply(pN,tsN), fun e -> EMethodApply(r, pT, tsON, tsTAbs @ [e], false)
      | TTuple ts ->
         let tsO,tsN,tsT = List.unzip3 (List.map tp ts)
         let T e = 
            match e with
            | ETuple es when es.Length = tsT.Length ->
               // optimization to avoid reducible expressions
               let tes = List.zip tsT es
               let eTs = List.map (fun (t,e) -> t e) tes
               ETuple(eTs)
            | _ ->
               let its = List.indexed tsT
               let esT = List.map (fun (i,t) -> t (EProj(e, i))) its
               ETuple(esT)
         TTuple tsO, TTuple tsN, T
      | TFun _ -> failwith (unsupported "function types")
      | TObject -> failwith (unsupported "object type") // TODO: check if t,t,id is sound here
      | TSeq t ->
         let tO,tN,tT = tp t
         TSeq tO, TSeq tN, fun e -> seqMap e tT
      | TSet t ->
         let tO,tN,tT = tp t
         TSet tO, TSet tN, fun e -> setMap e tT
      | TMap(s,t) ->
         let sO,sN,sT = tp s
         let tO,tN,tT = tp t
         TMap(sO,tO), TMap(sN,tN), fun e -> mapMap e sT tT
      | TArray t ->
         let tO,tN,tT = tp t
         TArray tO, TArray tN, fun e -> arrayMap e tT
      | TUnimplemented -> TUnimplemented, TUnimplemented, fun _ -> EUnimplemented
      
    /// translates expression e according to the translation function for its type
    /// pre: |- e:T
    and expr(e: Expr, t: Type): Expr*Expr*Condition =
       e,e,e //TODO
