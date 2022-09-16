namespace TypeInjections

open TypeInjections.YIL
open YIL

module Traverser =
    (*
       traverses YIL syntax
    
       Concrete implementations should implement the abstract methods for the cases relevant to the transformation.
       For all other cases, they should default to the XXXDefault methods,
       which traverse one level and then call the abstract methods again.
    *)

    [<AbstractClass>]
    type Transform() =
        abstract member error : string -> unit
        default this.error(s: string) =
            System.Console.WriteLine(s)
        
        
        /// translate a path referencing a declaration
        abstract member path : Context * Path -> Path
        default this.path(_,p) = p

        abstract member decl : Context * Decl -> Decl list
        abstract member tp : Context * Type -> Type
        abstract member expr : Context * Expr -> Expr
        abstract member prog : Program -> Program

        /// translate each expression in the context extended with all variable declarations made in previous expressions
        member this.exprList(ctx: Context, es: Expr list) =
            let mutable lds : LocalDecl list = [] // the var decls seen so far
            let exprWithLds(e: Expr) =
                let newCtx = ctx.add lds
                let eT = this.expr(newCtx, e)
                lds <- List.append lds (exprDecl e)
                eT
            List.map exprWithLds es
        /// translates an optional expression
        member this.exprO(ctx: Context, eO: Expr option) =
            Option.map (fun t -> this.expr (ctx, t)) eO

        /// translates a list of types
        member this.tpList(ctx: Context, ts: Type list) =
            List.map (fun t -> this.tp (ctx, t)) ts
        /// translates an optional type
        member this.tpO(ctx: Context, tO: Type option) =
            Option.map (fun t -> this.tp (ctx, t)) tO

        (* *****
           The this.XXXDefault methods transform an XXX by recursing one level into the syntax tree
           and calling the above abstract methods on the subobjects.

           The implementations below are straightforward but tedious.
        *)

        member this.progDefault(p: Program) : Program =
            let ctx = Context(p)
            let dsT =
                List.collect (fun (d: Decl) -> this.decl (ctx, d)) p.decls
            { name = p.name
              decls = dsT
              meta = p.meta }

        member this.importType(ctx: Context, e: ImportType) =
            match e with
            | ImportDefault p -> ImportDefault (this.path(ctx, p))
            | ImportOpened p ->  ImportOpened (this.path(ctx, p))
            | ImportEquals (lhs, rhs) -> ImportEquals (this.path(ctx, lhs), this.path(ctx, rhs))
        
        member this.exportType(ctx: Context, e: ExportType) =
            let path p = this.path(ctx, p)
            let provides = List.map path e.provides
            let reveals = List.map path e.reveals
            ExportType(provides, reveals)
            
        
        // transform a declaration
        member this.declDefault(ctx: Context, d: Decl) : Decl list =
            let childCtx (dName: string) (ctx: Context) = ctx.enter dName
            match d with
            | Include p -> [Include p]
            | Module (n, ds, m) ->
                let nameP = n.Split(".") |> List.ofArray
                let imports = List.choose (function | Import it -> Some it | _ -> None) ds
                let moduleCtx = List.fold
                                    (fun (ctx: Context) -> ctx.addImport) (ctx.enterModuleScope(Path(nameP))) imports
                let membersT =
                    List.collect (fun (d: Decl) -> this.decl (childCtx n moduleCtx, d)) ds
                [ Module(n, membersT, m) ]
            | Datatype (n, tpvs, cons, ds, a) ->
                // We enter a new module scope when in datatype constructors. For instance,
                // datatype "Option" inside Joint.CommonTypes should be in scope
                // Path ["Joint", "CommonTypes", "Option"].
                let bodyCtx = (childCtx n ctx).enterModuleScope(Path[n]).addTpvars tpvs
                let consT =
                    List.map (fun (c: DatatypeConstructor) -> this.constructor(bodyCtx, c)) cons
                let membersT =
                    List.collect (fun (d: Decl) -> this.decl (bodyCtx, d)) ds
                [ Datatype(n, tpvs, consT, membersT, a) ]
            | Class (n, isT, tpvs, ps, ds, m) ->
                // Enter a new module scope as well in class. TODO: check if this approach generates valid code.
                let bodyCtx = (childCtx n ctx).enterModuleScope(Path[n]).addTpvars tpvs
                let membersT =
                    List.collect (fun (d: Decl) -> this.decl (bodyCtx, d)) ds
                let psT = List.map (fun p -> this.classType(ctx, p)) ps
                [ Class(n, isT, tpvs, psT, membersT, m) ]
            | TypeDef (n, tpvs, sp, predO, isN, m) ->
                let ctxE = ctx.addTpvars tpvs
                let spT = this.tp(ctxE, sp)
                let predT = match predO with
                            | None -> None
                            | Some(x,p) -> Some(x, this.expr(ctxE, p))
                [ TypeDef(n, tpvs, spT, predT, isN, m) ]
            | Field (n, t, e, isG, isS, isM, m) ->
                [ Field(n, this.tp(ctx, t), this.exprO(ctx, e), isG, isS, isM, m) ]
            | Method (methodType, n, tpvs, ins, outs, modifies, reads, decreases, b, isG, isS, m) ->
                let ctxTps = (childCtx n ctx).addTpvars tpvs
                let insT = this.inputSpec(ctxTps, ins)
                let ctxIns = ctxTps.add(ins.decls)
                let outsT =
                    match outs with
                    | OutputSpec(ds,cs) -> OutputSpec(this.localDeclList(ctxIns, ds),
                                                      this.conditionList(ctxIns, cs))
                let modifiesT =
                    List.map (fun e -> this.expr(ctx, e)) modifies
                let readsT =
                    List.map (fun e -> this.expr(ctx, e)) reads
                let decreasesT =
                    List.map (fun e -> this.expr(ctx, e)) decreases
                let bodyCtx = (ctxIns.add outs.namedDecls).enterBody()
                let bT = Option.map (fun b -> this.expr (bodyCtx, b)) b
                [ Method(methodType, n, tpvs, insT, outsT, modifiesT, readsT, decreasesT, bT, isG, isS, m) ]
            | ClassConstructor (n, tpvs, ins, outs, b, m) ->
                let headerCtx = (childCtx n ctx).addTpvars tpvs
                let insT = this.inputSpec(headerCtx, ins)
                let outsT = this.conditionList(headerCtx, outs)
                let bodyCtx = (headerCtx.add ins.decls).enterBody()
                let bT = this.exprO(bodyCtx, b)
                [ ClassConstructor(n, tpvs, insT, outsT, bT, m) ]
            | Import importT -> [Import importT]
            | Export exportT -> [Export (this.exportType(ctx, exportT))]
            | DUnimplemented -> [ d ]

        // transforms a type
        member this.tpDefault(ctx: Context, tp: Type) =
            let rc (t: Type) = this.tp (ctx, t)
            let rcL (ts: Type list) = List.map rc ts
            match tp with
            | TUnit
            | TBool
            | TChar
            | TString _
            | TNat _
            | TInt _
            | TReal _
            | TObject 
            | TBitVector _
            | TVar _ -> tp
            | TApply (op, args) -> TApply(this.path(ctx,op), rcL args)
            | TApplyPrimitive (op, t) -> TApplyPrimitive(this.path(ctx, op), rc t)
            | TTuple ts -> TTuple (rcL ts)
            | TSeq(b,t) -> TSeq (b, rc t)
            | TSet(b,t) -> TSet (b, rc t)
            | TMap (b, d, r) -> TMap (b,rc d, rc r)
            | TArray(b,t) -> TArray (b,rc t)
            | TFun (ins,out) -> TFun (rcL ins, rc out)
            | TNullable t -> TNullable (rc t)
            | TUnimplemented -> TUnimplemented

        // transforms an expression
        member this.exprDefault(ctx: Context, expr: Expr) : Expr =
            let rcE (e: Expr) = this.expr (ctx, e)
            let rcT (t: Type) = this.tp (ctx, t)
            let rcEs (es: Expr list) = List.map rcE es
            let rcEo (eO: Expr option) = Option.map rcE eO
            let rcTs (ts: Type list) = List.map rcT ts
            match expr with
                | EVar _
                | EThis
                | EReal _
                | EInt _
                | EBool _
                | EChar _
                | EString _ -> expr
                | ENew (ct, args) ->
                    let ctT = this.classType (ctx, ct)
                    ENew(ctT, rcEs args)
                | EMemberRef (r, m, ts) -> EMemberRef (this.receiver(ctx, r), this.path(ctx,m), (rcTs ts))
                | EMethodApply (r, m, ts, es, isG) ->
                    EMethodApply(this.receiver(ctx, r), this.path(ctx,m), rcTs ts, rcEs es, isG)
                | EConstructorApply (c, ts, es) -> EConstructorApply(this.path(ctx, c), rcTs ts, rcEs es)
                | EQuant (q, lds, r, b) ->
                    let ctxE = ctx.add lds
                    let rT = this.exprO(ctxE, r)
                    let bT = this.expr(ctxE, b)
                    EQuant(q, this.localDeclList (ctx, lds), rT, bT)
                | EOld e -> EOld (rcE e)
                | ETuple es -> ETuple (rcEs es)
                | EProj (e, i) -> EProj (rcE e, i)
                | ESet (t, es) -> ESet (rcT t, rcEs es)
                | ESetComp (lds, p) ->
                    let ctxE = ctx.add lds
                    let pT = this.expr(ctxE, p)
                    ESetComp (this.localDeclList (ctx, lds), pT)
                | ESeq (t, es) -> ESeq (rcT t, rcEs es)
                | ESeqConstr(t, l, i) -> ESeqConstr(rcT t, rcE l, rcE i)
                | ESeqAt (s, i) -> ESeqAt (rcE s, rcE i)
                | ESeqRange (s, f, t) -> ESeqRange (rcE s, rcEo f, rcEo t)
                | ESeqUpdate (s, i, e) -> ESeqUpdate (rcE s, rcE i, rcE e)
                | ECharAt (s, i) -> ECharAt (rcE s, rcE i)
                | EStringRange (s, f, t) -> EStringRange (rcE s, rcEo f, rcEo t)
                | EToString es -> EToString (rcEs es)
                | EArray (t, dim) -> EArray (rcT t, dim)
                | EArrayAt (a, i) -> EArrayAt (rcE a, i)
                | EArrayRange (a, f, t) -> EArrayRange (rcE a, rcEo f, rcEo t)
                | EArrayUpdate (a, i, e) -> EArrayUpdate (rcE a, i ,rcE e)
                | EMapAt (m, a) -> EMapAt (rcE m, a)
                | EMapKeys m -> EMapKeys (rcE m)
                | EMapDisplay kvs ->
                    (List.fold (fun l (eKey, eVal) -> (rcE eKey, rcE eVal) :: l) [] kvs)
                    |> List.rev
                    |> EMapDisplay
                | EMapComp (lds, p, tL, tR) ->
                    let ctxE = ctx.add lds
                    let pT = this.expr(ctxE, p)
                    let pTL = Option.map (fun e -> this.expr(ctxE, e)) tL 
                    let pTR = this.expr(ctxE, tR)
                    EMapComp (this.localDeclList (ctx, lds), pT, pTL, pTR)
                | EFun(ins, out, bd) -> EFun(this.localDeclList(ctx,ins), rcT out, this.expr(ctx.add ins, bd))
                | EAnonApply (f, es) -> EAnonApply(rcE f, rcEs es)
                | EUnOpApply (op, e) -> EUnOpApply(op, rcE e)
                | EBinOpApply (op, e1, e2) -> EBinOpApply(op, rcE e1, rcE e2)
                | ELet(n,tp,df,bd) -> ELet(n, rcT tp, rcE df, this.expr(ctx.add(n,tp), bd))
                | ETypeConversion (e, t) -> ETypeConversion (rcE e, rcT t)
                | ETypeTest (e, t) -> ETypeTest (rcE e, rcT t)
                | EBlock es ->
                    let esT = this.exprList (ctx, es)
                    EBlock esT
                | EIf (c, t, e) ->
                    // Similar to the `EBlock` case, we reset the next statement but keep information on whether
                    // this statement is last: if this statement is last then the last statement of the then and else
                    // branch is also last
                    EIf(rcE c, rcE t, rcEo e)
                | EFor (index, init, ls, up, body) ->
                    let innerCtx = ctx.add [index]
                    let bodyT = this.expr (innerCtx, body)
                    EFor (this.localDecl(ctx, index), rcE init, rcE ls, up, bodyT)
                | EWhile (c, e, l) -> EWhile (rcE c, rcE e,  l)
                | EReturn es -> EReturn (rcEs es)
                | EBreak _ -> expr
                | EMatch (e, t, cases, d) ->
                    let csT = List.map (fun (c: Case) -> this.case (ctx, c)) cases
                    let dfltT = this.exprO(ctx, d)
                    EMatch(rcE e, rcT t, csT, dfltT)
                | EDecls(ds) ->
                    let dsT = List.map (fun (ld,upO) -> (this.localDecl(ctx,ld),
                                                         Option.map (fun u -> this.updateRHS(ctx, u)) upO)) ds
                    EDecls(dsT)
                | EUpdate (es, rhs) -> EUpdate (rcEs es, this.updateRHS(ctx,rhs))
                | EDeclChoice (ld, e) ->
                    let eT = this.expr (ctx.add [ld], e) // e is a predicate about n and thus can see it
                    EDeclChoice (this.localDecl (ctx, ld), eT)
                | ENull(t) -> ENull(rcT t)
                | EPrint es -> EPrint (rcEs es)
                | EAssert e -> EAssert (rcE e)
                | EAssume e -> EAssume (rcE e)
                | EReveal es -> EReveal (rcEs es)
                | EExpect e -> EExpect (rcE e)
                | ECommented(s,e) -> ECommented(s, rcE e)
                | ETypeTest(e, t) -> ETypeTest(rcE e, rcT t)
                | EUnimplemented -> expr

        // methods for auxiliary types

        /// transforms a variable declaration
        abstract member localDecl : Context * LocalDecl -> LocalDecl

        default this.localDecl(ctx, ld) =
            LocalDecl(ld.name, this.tp(ctx,ld.tp), ld.ghost)

        abstract member updateRHS : Context * UpdateRHS -> UpdateRHS
        default this.updateRHS(ctx: Context, u: UpdateRHS) =
            { df = this.expr (ctx, u.df)
              monadic = this.tpO (ctx, u.monadic) }

        // transforms input specifications
        abstract member inputSpec : Context * InputSpec -> InputSpec
        default this.inputSpec(ctx, ins) =
           match ins with
           | InputSpec(lds, cs) ->
               let ci = ctx.add lds
               InputSpec(this.localDeclList(ctx, lds), this.conditionList(ci,cs))
            
        
        /// convenience method for the common case of lists of declarations
        abstract member localDeclList : Context * LocalDecl list -> LocalDecl list
        default this.localDeclList(ctx, lds) =
            // we're simply-typed and declarations do not contain expressions, so all declarations can use the same context
            List.map (fun (d: LocalDecl) -> this.localDecl (ctx, d)) lds

        /// transforms a condition
        abstract member condition : Context * Condition -> Condition
        default this.condition(ctx, c) =
            this.expr(ctx, c)

        /// convenience method for the common case of lists of declarations
        abstract member conditionList : Context * Condition list -> Condition list
        default this.conditionList(ctx, cs) =
            List.map (fun (c: Condition) -> this.condition(ctx, c)) cs

        /// transforms a class type
        abstract member classType : Context * ClassType -> ClassType
        default this.classType(ctx, ct) =
            { path = this.path(ctx,ct.path)
              tpargs = List.map (fun (t: Type) -> this.tp (ctx, t)) ct.tpargs }

        /// transforms a receiver
        abstract member receiver : Context * rcv: Receiver -> Receiver
        default this.receiver(ctx, rcv) =
            match rcv with
            | StaticReceiver ct -> StaticReceiver(this.classType (ctx, ct))
            | ObjectReceiver e -> ObjectReceiver(this.expr (ctx, e))

        /// transforms a constructor in a datatype
        abstract member constructor : Context * cons: DatatypeConstructor -> DatatypeConstructor
        default this.constructor(ctx, cons) =
            let insT =
                this.localDeclList (ctx, cons.ins)
            { name = cons.name
              ins = insT
              meta = cons.meta }

        /// transforms a case in a pattern match
        abstract member case : Context * case: Case -> Case
        default this.case(ctx, case) =
            let varsT = this.localDeclList(ctx, case.vars)
            let ctxE = ctx.add case.vars
            let patternT = this.expr(ctxE, case.pattern)
            let bodyT = this.expr (ctxE, case.body)
            { vars = varsT
              pattern = patternT
              body = bodyT
            }
    // ***** some concrete implementations for examples and testing

    (* identity transformation: implements every translation method by delegating to the default implementation
       log: if true, print some info while traversing
    *)
    type Identity() =
        inherit Transform()
        override this.decl(ctx: Context, d: Decl) = base.declDefault (ctx, d)
        override this.tp(ctx: Context, t: Type) = base.tpDefault (ctx, t)
        override this.expr(ctx: Context, e: Expr) = base.exprDefault (ctx, e)
        override this.prog(prog: Program) = base.progDefault(prog)


    (* checks that all identifiers references can be resolved; identity otherwise *)
    type CheckReferences() =
        inherit Identity()

        override this.tp(ctx: Context, t: Type) =
            match t with
            | TVar n ->
                let c = (List.filter (fun (a,_) -> a = n) ctx.tpvars).Length
                if c > 1 then
                    // We are prescriptive here and treat shadowing as an error
                    this.error($"shadowing of type variable {n} at {ctx}")
                if c = 0 then
                    this.error($"undeclared type variable {n} at {ctx}")
            | TApply (op,_) -> lookupByPath (ctx.prog, op) |> ignore
            | _ -> ()
            base.tpDefault (ctx, t)

        override this.expr(ctx: Context, e: Expr) =
            match e with
            | EVar (name = n) ->
                let c = Utils.listCount (List.map localDeclName ctx.vars, n)
                if c > 1 then
                    // We are prescriptive here and treat shadowing as an error
                    this.error($"shadowing of variable {n}")
                if c = 0 then
                    this.error("undeclared variable")
                ()
            | EMemberRef (mmbr = p)
            | EMethodApply (method = p) ->
                lookupByPath (ctx.prog, p) |> ignore
                ()
            | EConstructorApply (cons = p) ->
                lookupConstructor (ctx.prog, p) |> ignore
                ()
            | _ -> ()
            base.exprDefault (ctx, e)

    (* transformation for performing a type substitution; this should only be applied to types or expressions *)
    type SubstituteTypes(subs: (string * Type) list) =
        inherit Identity()

        override this.tp(ctx: Context, tp: Type) =
            // types cannot be bound inside a type, so no capture possible
            match tp with
            | TVar n ->
                let tO = List.tryFind (fun x -> fst x = n) subs
                match tO with
                | None -> tp
                | Some (_, t) -> t
            | _ -> this.tpDefault (ctx, tp)

    /// substitution for type variables
    let substituteTypes (ctx: Context, subs: (string * Type) list, t: Type) : Type =
        let sub = SubstituteTypes(subs)
        sub.tp (ctx, t)
    /// substitution for type variables in an expression
    let substituteTypesInExpr (ctx: Context, subs: (string * Type) list, e: Expr) : Expr =
        let sub = SubstituteTypes(subs)
        sub.expr (ctx, e)

    (* transformation for performing an expression substitution; this should only be applied to expressions *)
    type SubstituteExprs(fromCtx: Context, toCtx: Context, subs: (string * Expr) list) =
        inherit Identity()

        override this.expr(ctx: Context, e: Expr) =
            match e with
            | EVar n ->
                // the initial context is passed to the traverser, and traversal starts with the empty context
                // thus, any names in the traversal context were bound during traversal and are not substituted
                // other names must have been declared in the initial context and are substituted
                if ctx.lookupLocalDeclO(n).IsSome then
                    e
                else
                    let eO = List.tryFind (fun x -> fst x = n) subs
                    match eO with
                    | None -> e // we allow substitutions to be partial
                    | Some (_, s) ->
                        if Utils.listDisjoint(List.map localDeclName toCtx.vars, List.map localDeclName ctx.vars) then
                            s
                        else
                            // capture-avoidance should be when/if practical inputs need it
                            failwith("implementation limitation: possible variable capture")
            | _ -> this.exprDefault (ctx, e)

    /// substitution for expression variables
    let substituteExprs (f: Context, t: Context, subs: (string * Expr) list, e: Expr) : Expr =
        let sub = SubstituteExprs(f,t, subs)
        sub.expr (Context(f.prog), e)

    /// transformation to apply basic term normalization
    /// topOnly: reduce only one step at toplevel (if any)
    type Reduce(topOnly:bool) =
        inherit Identity()
        override this.expr(ctx: Context, e: Expr) =
          let eR =
           match e with
           | EProj(ETuple(ts),i) ->
               // beta-reduction for tuples: (t_1,...,t_n).i --->  t_i
               ts.Item i
           | ETuple(es) ->
               let isEtaExp = List.indexed es |> List.forall fun (i,e) -> e = EProj(E)
           | EAnonApply(EFun(lds,_,b), es) when lds.Length = es.Length ->
               // beta-reduction: (fun x_1,...,x_n -> b) e_1 ... e_n ---> b[x_1/e_1,...,x_n/e_n] 
               let subs = (List.zip lds es) |> List.map (fun (ld,e) -> ld.name,e)
               substituteExprs(ctx.add(lds), ctx, subs, b)
           | EFun(lds,_,EAnonApply(EVar(f), args)) when lds.Length = args.Length ->
               // eta-contraction: fun x_1, ..., x_n -> f x_1 ... x_n ---> f
               // covers only special case where f is variable
               let isEtaExp = List.zip lds args |> List.forall (fun (ld,a) -> a = EVar(ld.name))
               if isEtaExp then EVar(f) else e
           | _ -> e
          if topOnly then
             eR
          else
             if e = eR then this.exprDefault(ctx, e) else this.expr(ctx, e)
    /// basic term normalization
    let reduce(ctx: Context, e: Expr) = Reduce(true).expr(ctx,e)
    
    /// test the traverser class by running a deep identity transformation on a program
    let test(p: Program) =
        let id = Identity()
        let pT = id.prog(p)
        if pT <> p then
            failwith("implementation error in traverser")
        else
            System.Console.WriteLine("***** traversal OK")