namespace TypeInjections

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

        override this.elem(ctxO: Context, ctxN: Context, dD: Diff.Elem<'y, 'd>, td: Context * Context * 'd -> 'd) =
            match dD with
            | Diff.Same _
            | Diff.Add _ -> dD
            | Diff.Delete _ ->
                this.addPath (ctxO, ctxO.currentDecl)
                dD
            | Diff.Update (d, n, df) ->
                this.addPath (ctxO, ctxO.currentDecl)
                Diff.Update(d, n, td (ctxO, ctxN, df))

        override this.decl(ctxO: Context, ctxN: Context, d: Diff.Decl) =
            Option.map (fun (n: Diff.Name) -> this.addPath (ctxO, ctxO.currentDecl.child (n.getOld))) d.nameO
            |> ignore

            this.declDefault (ctxO, ctxN, d)

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
