namespace TypeInjections

open TypeInjections.Diff
open TypeInjections.YIL

module DiffTraverser =
    (*
       traverses Diff syntax

       Concrete implementations should implement the abstract methods for the cases relevant to the transformation.
       For all other cases, they should default to the XXXDefault methods,
       which traverse one level and then call the abstract methods again.
    *)

    [<AbstractClass>]
    type Transform() =
        abstract member error : string -> unit
        default this.error(s: string) = System.Console.WriteLine(s)

        abstract member list :
            Context * Context * Diff.List<'y, 'd> * (Context * Context * 'y * 'y * 'd -> 'd) ->
            Diff.List<'y, 'd>

        abstract member elem :
            Context * Context * Diff.Elem<'y, 'd> * (Context * Context * 'y * 'y * 'd -> 'd) ->
            Diff.Elem<'y, 'd>

        default this.list
            (
                ctxO: Context,
                ctxN: Context,
                dsD: Diff.List<'y, 'd>,
                td: Context * Context * 'y * 'y * 'd -> 'd
            ) =
            Diff.UpdateList(List.map (fun dD -> this.elem (ctxO, ctxN, dD, td)) dsD.elements)

        default this.elem
            (
                ctxO: Context,
                ctxN: Context,
                dD: Diff.Elem<'y, 'd>,
                td: Context * Context * 'y * 'y * 'd -> 'd
            ) =
            match dD with
            | Diff.Same _
            | Diff.Add _
            | Diff.Delete _ -> dD
            | Diff.Update (d, n, df) -> Diff.Update(d, n, td (ctxO, ctxN, d, n, df))

        /// specialization for decl list
        abstract member declList : Context * Context * Diff.List<Decl, Diff.Decl> -> Diff.List<Decl, Diff.Decl>

        default this.declList(ctxO: Context, ctxN: Context, dsD: Diff.List<Decl, Diff.Decl>) =
            Diff.UpdateList(List.map (fun dD -> this.elem (ctxO, ctxN, dD, this.decl)) dsD.elements)

        abstract member name : Context * Context * Diff.Name -> Diff.Name
        default this.name(ctxO: Context, ctxN: Context, name: Diff.Name) = name

        abstract member tp : Context * Context * Diff.Type -> Diff.Type
        default this.tp(ctxO: Context, ctxN: Context, t: Diff.Type) = t

        abstract member methodType : Context * Context * Diff.MethodType -> Diff.MethodType
        default this.methodType(ctxO: Context, ctxN: Context, methodType: Diff.MethodType) = methodType

        abstract member typearg : Context * Context * TypeArg * TypeArg * Diff.TypeArg -> Diff.TypeArg
        default this.typearg(ctxO: Context, ctxN: Context, tO: TypeArg, tN: TypeArg, t: Diff.TypeArg) = t

        abstract member classtype : Context * Context * ClassType * ClassType * Diff.ClassType -> Diff.ClassType
        default this.classtype(ctxO: Context, ctxN: Context, ctO: ClassType, ctN: ClassType, ct: Diff.ClassType) = ct

        abstract member condition : Context * Context * Condition * Condition * Diff.Condition -> Diff.Condition

        default this.condition(ctxO: Context, ctxN: Context, condO: Condition, condN: Condition, cond: Diff.Condition) =
            cond

        abstract member exprO : Context * Context * Diff.ExprO -> Diff.ExprO

        default this.exprO(ctxO: Context, ctxN: Context, e: Diff.ExprO) = e

        abstract member localDecl : Context * Context * LocalDecl * LocalDecl * Diff.LocalDecl -> Diff.LocalDecl

        default this.localDecl(ctxO: Context, ctxN: Context, ldO: LocalDecl, ldN: LocalDecl, ld: Diff.LocalDecl) =
            match ld with
            | Diff.LocalDecl (n, t) -> Diff.LocalDecl(this.name (ctxO, ctxN, n), this.tp (ctxO, ctxN, t))

        abstract member datatypeConstructor :
            Context * Context * DatatypeConstructor * DatatypeConstructor * Diff.DatatypeConstructor ->
            Diff.DatatypeConstructor

        default this.datatypeConstructor
            (
                ctxO: Context,
                ctxN: Context,
                dcO: DatatypeConstructor,
                dcN: DatatypeConstructor,
                dc: Diff.DatatypeConstructor
            ) =
            match dc with
            | Diff.DatatypeConstructor (n, lds) ->
                Diff.DatatypeConstructor(this.name (ctxO, ctxN, n), this.list (ctxO, ctxN, lds, this.localDecl))

        abstract member inputSpec : Context * Context * Diff.InputSpec -> Diff.InputSpec

        default this.inputSpec(ctxO: Context, ctxN: Context, spec: Diff.InputSpec) =
            Diff.InputSpec(
                this.list (ctxO, ctxN, spec.decls, this.localDecl),
                this.list (ctxO, ctxN, spec.conditions, this.condition)
            )

        abstract member outputSpec : Context * Context * Diff.OutputSpec -> Diff.OutputSpec

        default this.outputSpec(ctxO: Context, ctxN: Context, spec: Diff.OutputSpec) =
            Diff.OutputSpec(
                this.list (ctxO, ctxN, spec.decls, this.localDecl),
                this.list (ctxO, ctxN, spec.conditions, this.condition)
            )

        abstract member prog : Context * Context * Diff.Program -> Diff.Program

        member this.progDefault(ctxO: Context, ctxN: Context, prog: Diff.Program) =
            { name = prog.name
              decls = this.declList (ctxO, ctxN, prog.decls) }

        abstract member decl : Context * Context * Decl * Decl * Diff.Decl -> Diff.Decl

        member this.declDefault(ctxO: Context, ctxN: Context, declO: Decl, declN: Decl, d: Diff.Decl) =
            let name n = this.name (ctxO, ctxN, n)

            let decls ctxOb ctxNb ds = this.declList (ctxOb, ctxNb, ds)

            let typeargs ctxOb ctxNb ts =
                this.list (ctxOb, ctxNb, ts, this.typearg)

            let classtypes ctxOb ctxNb cs =
                this.list (ctxOb, ctxNb, cs, this.classtype)

            let datatypeConstructors ctxOb ctxNb dcs =
                this.list (ctxOb, ctxNb, dcs, this.datatypeConstructor)

            let conditions ctxOb ctxNb conds =
                this.list (ctxOb, ctxNb, conds, this.condition)

            match d with
            | Diff.Module (n, ds) ->
                let imports =
                    List.choose
                        (function
                        | Import it -> Some it
                        | _ -> None)

                let ctxOm =
                    List.fold
                        (fun (ctx: Context) -> ctx.addImport)
                        (ctxO.enter(n.getOld).clearImport ())
                        (imports (ds.getOld ()))

                let ctxNm =
                    List.fold
                        (fun (ctx: Context) -> ctx.addImport)
                        (ctxN.enter(n.getNew).clearImport ())
                        (imports (ds.getNew ()))

                Diff.Module(name n, decls ctxOm ctxNm ds)
            | Diff.Class (n, ts, cs, ds) ->
                let ctxOb =
                    ctxO.enter(n.getOld).addTpvars (ts.getOld ())

                let ctxNb =
                    ctxN.enter(n.getNew).addTpvars (ts.getNew ())

                Diff.Class(name n, typeargs ctxOb ctxNb ts, classtypes ctxOb ctxNb cs, decls ctxOb ctxNb ds)
            | Diff.Datatype (n, ts, dcs, ds) ->
                let ctxOb =
                    ctxO.enter(n.getOld).addTpvars (ts.getOld ())

                let ctxNb =
                    ctxN.enter(n.getNew).addTpvars (ts.getNew ())

                Diff.Datatype(
                    name n,
                    typeargs ctxOb ctxNb ts,
                    datatypeConstructors ctxOb ctxNb dcs,
                    decls ctxOb ctxNb ds
                )
            | Diff.ClassConstructor (n, ts, ins, conds, e) ->
                let ctxOh =
                    ctxO.enter(n.getOld).addTpvars (ts.getOld ())

                let ctxNh =
                    ctxN.enter(n.getNew).addTpvars (ts.getNew ())

                let ctxOb =
                    ctxOh.add(ins.decls.getOld ()).enterBody ()

                let ctxNb =
                    ctxNh.add(ins.decls.getNew ()).enterBody ()

                Diff.ClassConstructor(
                    name n,
                    typeargs ctxOh ctxNh ts,
                    this.inputSpec (ctxOh, ctxNh, ins),
                    conditions ctxOh ctxNh conds,
                    this.exprO (ctxOb, ctxNb, e)
                )
            | Diff.TypeDef (n, ts, t, e) ->
                let ctxOe =
                    ctxO.enter(n.getOld).addTpvars (ts.getOld ())

                let ctxNe =
                    ctxN.enter(n.getNew).addTpvars (ts.getNew ())

                Diff.TypeDef(name n, typeargs ctxOe ctxNe ts, this.tp (ctxOe, ctxNe, t), this.exprO (ctxOe, ctxNe, e))
            | Diff.Field (n, t, e) ->
                let ctxOe = ctxO.enter (n.getOld)
                let ctxNe = ctxN.enter (n.getNew)
                Diff.Field(name n, this.tp (ctxOe, ctxNe, t), this.exprO (ctxOe, ctxNe, e))
            | Diff.Method (n, methodType, ts, ins, outs, e) ->
                let ctxOh =
                    ctxO.enter(n.getOld).addTpvars (ts.getOld ())

                let ctxNh =
                    ctxN.enter(n.getNew).addTpvars (ts.getNew ())

                let ctxOi = ctxOh.add (ins.decls.getOld ())
                let ctxNi = ctxNh.add (ins.decls.getNew ())

                let ctxOb =
                    ctxOi.add(outs.namedDecls.getOld ()).enterBody ()

                let ctxNb =
                    ctxNi.add(outs.namedDecls.getNew ()).enterBody ()

                Diff.Method(
                    name n,
                    this.methodType (ctxO, ctxN, methodType),
                    typeargs ctxOh ctxNh ts,
                    this.inputSpec (ctxOh, ctxNh, ins),
                    this.outputSpec (ctxOi, ctxNi, outs),
                    this.exprO (ctxOb, ctxNb, e)
                )
            | Diff.Import importT -> Diff.Import importT
            | Diff.Export exportT -> Diff.Export exportT
            | Diff.DUnimplemented -> Diff.DUnimplemented

    (* identity transformation: implements every translation method by delegating to the default implementation
    *)
    type Identity() =
        inherit Transform()

        override this.decl(ctxO: Context, ctxN: Context, declO: Decl, declN: Decl, d: Diff.Decl) =
            base.declDefault (ctxO, ctxN, declO, declN, d)

        override this.prog(ctxO: Context, ctxN: Context, prog: Diff.Program) = base.progDefault (ctxO, ctxN, prog)
