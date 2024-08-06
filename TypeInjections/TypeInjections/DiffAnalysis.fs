namespace TypeInjections

open TypeInjections.Diff
open TypeInjections.YIL

module DiffAnalysis =
    /// Returns the set of non-module decls (in Set<Path>) that are directly changed or deleted from the old program
    type GatherChangedOrDeleted() =
        inherit DiffTraverser.Identity()

        let mutable result : Set<Path> = Set.empty

        member this.addPath(ctxO: Context, p: Path) =
            if ctxO.lookupByPath(p).isModule () then
                // Do not add modules to the result.
                ()
            else
                result <- result.Add(p)

        override this.name(ctxO: Context, ctxN: Context, name: Diff.Name) =
            match name with
            | Rename _ -> this.addPath (ctxO, ctxO.currentDecl)
            | SameName _ -> ()

            name

        override this.tp(ctxO: Context, ctxN: Context, t: Diff.Type) =
            match t with
            | UpdateType _ -> this.addPath (ctxO, ctxO.currentDecl)
            | SameType _ -> ()

            t

        override this.exprO(ctxO: Context, ctxN: Context, e: Diff.ExprO) =
            match e with
            | SameExprO _ -> ()
            | AddExpr _ // adding an expr is a change (not addition) to the parent decl
            | DeleteExpr _
            | UpdateExpr _ -> this.addPath (ctxO, ctxO.currentDecl)

            e

        override this.elem(ctxO: Context, ctxN: Context, dD: Diff.Elem<'y, 'd>, td: Context * Context * 'y * 'y * 'd -> 'd) =
            match dD with
            | Diff.Same _
            | Diff.Add _ -> dD
            | Diff.Delete _ ->
                this.addPath (ctxO, ctxO.currentDecl)
                dD
            | Diff.Update (d, n, df) ->
                this.addPath (ctxO, ctxO.currentDecl)
                Diff.Update(d, n, td (ctxO, ctxN, d, n, df))

        override this.declList(ctxO: Context, ctxN: Context, dsD: Diff.List<Decl, Diff.Decl>) =
            // Ignore any changes on lemmas
            Diff.UpdateList(
                List.map
                    (fun (dD: Diff.Elem<Decl, Diff.Decl>) ->
                        match dD with
                        | Diff.Same d
                        | Diff.Add d
                        | Diff.Delete d when d.isLemma () -> dD
                        | Diff.Update (d, n, _) when d.isLemma () && n.isLemma () -> dD
                        | _ -> this.elem (ctxO, ctxN, dD, this.decl))
                    dsD.elements
            )

        member this.gather(ctxO: Context, ctxN: Context, prog: Diff.Program) =
            this.prog (ctxO, ctxN, prog) |> ignore
            result

    /// Returns the set of decls (in Set<Path>) that are directly or indirectly changed or deleted from the old program
    let changedInOld (ctxO: Context, ctxN: Context, progD: Diff.Program) =
        let changedDirectly =
            GatherChangedOrDeleted()
                .gather (ctxO, ctxN, progD)

        System.Console.WriteLine("********* changed directly *****")
        Set.iter (fun (p: Path) -> System.Console.WriteLine(p.ToString())) changedDirectly
        System.Console.WriteLine("***** END changed directly *****")

        let closure =
            Analysis.dependencyClosureByGatherDeclsUsingPaths (ctxO.prog, changedDirectly)

        closure
    
    /// Gather all specialized lemmas to generate in the proof sketch.
    type GatherSpecializedLemmaToGenerate(generateLemmaOrAxiomFor: Path -> bool) =
        inherit DiffTraverser.Identity()
        
        let mutable specializedCalls: Map<Path, Expr list> = Map.empty
        
        let generateLemmaOrAxiomForExpr (e: Expr) : bool =
            match e with
            | EMemberRef (_, m, _) -> generateLemmaOrAxiomFor m
            | _ -> false
        
        override this.elem
            (
                ctxO: Context,
                ctxN: Context,
                dD: Diff.Elem<'y, 'd>,
                td: Context * Context * 'y * 'y * 'd -> 'd
            ) =
            match dD with
            | Diff.Same d ->
                match box (d, td) with
                | :? (Decl * (Context * Context * Decl * Decl * Diff.Decl -> Diff.Decl)) as (d, td) ->
                    td (ctxO, ctxN, d, d, Diff.idDecl d) |> ignore // declSameOrUpdate
                    dD
                | _ -> dD
            | Diff.Add _
            | Diff.Delete _ -> dD
            | Diff.Update (d, n, df) -> Diff.Update(d, n, td (ctxO, ctxN, d, n, df))
        override this.decl(ctxO: Context, ctxN: Context, declO: Decl, declN: Decl, d: Diff.Decl) =
            let n = declO.name
            let p = ctxO.currentDecl.child (n)
            match d with
            | Diff.Method (nameD, tvsD, insD, outsD, bdD) when generateLemmaOrAxiomFor (p) ->
                match declO, declN with
                | Method(methodType = IsLemma), _
                | Method(methodType = IsMethod), _ -> ()
                | Method (_, _, tvs_o, ins_o, outs_o, modifiesO, readsO, decreasesO, bodyO, _, isStatic, isOpaqueO, _),
                  Method (_, _, tvs_n, ins_n, outs_n, modifiesN, readsN, decreasesN, _, _, _, isOpaqueN, _) ->
                    let ctxOh = ctxO.enter(nameD.getOld).addTpvars (tvsD.getOld ())
                    let ctxOi = ctxOh.add (insD.decls.getOld ())
                    let ctxOb = ctxOi.add(outsD.namedDecls.getOld ()).enterBody ()
                    match bodyO with
                    | Some bd ->
                        specializedCalls <- Analysis.GatherSpecializedLemmaCalls(generateLemmaOrAxiomForExpr)
                                                .gather(ctxOb, bd, specializedCalls)
                        ()
                    | _ -> ()
                | _ -> ()
            | _ -> ()
            this.declDefault(ctxO, ctxN, declO, declN, d)
        
        member this.gather(ctxO: Context, ctxN: Context, prog: Diff.Program) =
            this.prog(ctxO, ctxN, prog) |> ignore
            specializedCalls
