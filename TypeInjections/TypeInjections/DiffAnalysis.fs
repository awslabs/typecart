namespace TypeInjections

open TypeInjections.YIL

module DiffAnalysis =
    /// Returns the set of decls (in Set<Path>) that are directly changed or deleted from the old program
    type GatherChangedOrDeleted() =
        inherit DiffTraverser.Identity()

        let mutable result : Set<Path> = Set.empty

        override this.elem(ctxO: Context, ctxN: Context, dD: Diff.Elem<'y, 'd>, td: Context * Context * 'd -> 'd) =
            match dD with
            | Diff.Same _
            | Diff.Add _ -> dD
            | Diff.Delete _ ->
                result <- result.Add(ctxO.currentDecl)
                dD
            | Diff.Update (d, n, df) ->
                result <- result.Add(ctxO.currentDecl)
                Diff.Update(d, n, td (ctxO, ctxN, df))

        member this.gather(ctxO: Context, ctxN: Context, prog: Diff.Program) =
            this.prog (ctxO, ctxN, prog) |> ignore
            result

    /// Returns the set of decls (in Set<Path>) that are directly or indirectly changed or deleted from the old program
    let changedInOld (ctxO: Context, ctxN: Context, progD: Diff.Program) =
        let start =
            GatherChangedOrDeleted()
                .gather (ctxO, ctxN, progD)

        let closure =
            Analysis.dependencyClosureByGatherDeclsUsingPaths (ctxO.prog, start)

        closure
