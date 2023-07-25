namespace TypeInjections

open TypeInjections.YIL

/// diffs two YIL AST items and returns the corresponding AST item in Diff._
module Differ =

    /// compares two sets (given as lists)
    /// similar(o,n) = true iff n != o but n is updated version of o
    /// diff(o,n): if similar(o,n) produce Some(diff o n), unspecified otherwise
    let rec complexSet<'y, 'd when 'y: equality>
        (
            old: 'y list,
            nw: 'y list,
            similar: 'y * 'y -> bool,
            diff: 'y * 'y -> 'd option
        ) : Diff.List<'y, 'd> =
        let mutable nwDiffed : 'y list = []

        let diffOne o =
            if List.contains o nw then
                nwDiffed <- o :: nwDiffed
                Diff.Same o
            else
                match List.tryFind (fun n -> similar (o, n)) nw with
                | Some n ->
                    nwDiffed <- n :: nwDiffed
                    let d = Option.get (diff (o, n)) // succeeds by precondition
                    Diff.Update(o, n, d)
                | None -> Diff.Delete o

        let changed = List.map diffOne old
        // append Add for the elements of nw that have not been used by diffOne
        let diff =
            changed
            @ (List.map Diff.Add (Utils.listDiff (nw, nwDiffed)))

        Diff.UpdateList(diff)

    /// compares two sets (given as sets)
    /// compare elements only by equality and never generates an update between two elements
    and simpleSet<'y, 'd when 'y: equality> (old: 'y list, nw: 'y list) : Diff.List<'y, 'd> =
        complexSet (old, nw, (fun _ -> false), (fun _ -> None))

    /// compares two (ordered) lists
    /// see also complexSet
    and complexList<'y, 'd when 'y: equality>
        (
            old: 'y list,
            nw: 'y list,
            similar: 'y * 'y -> bool,
            diff: 'y * 'y -> 'd option
        ) =
        let mutable nwLeft = nw

        let diffOne o =
            if nwLeft.IsEmpty then
                // old declarations deleted at the end
                [ Diff.Delete o ]
            else
                let iO =
                    List.tryFindIndex (fun n -> similar (o, n)) nwLeft

                match iO with
                | Some i ->
                    // similar element comes later, assume everything in between (if anything) is added
                    let added, left = List.splitAt i nwLeft
                    nwLeft <- left
                    let n = nwLeft.Head
                    nwLeft <- nwLeft.Tail
                    // the diff between the two similar elements
                    let elem =
                        if o = n then
                            Diff.Same o
                        else
                            let d = Option.get (diff (o, n)) // succeeds by precondition
                            Diff.Update(o, n, d)
                    // now o = n
                    (List.map Diff.Add added) @ [ elem ]
                | None ->
                    // no similar elements occurs later, assume deleted
                    [ Diff.Delete o ]

        let changed = List.collect diffOne old
        // append new additions at the end
        let diff = changed @ List.map Diff.Add nwLeft
        Diff.UpdateList(diff)

    /// compares two (ordered) lists without comparing elements
    /// see also simpleSet
    and simpleList<'y, 'd when 'y: equality> (old: 'y list, nw: 'y list) =
        // 'diff' function is irrelevant if 'similar' is always false
        complexList (old, nw, (fun _ -> false), (fun _ -> None))

    /// diff between two names
    let rec name (old: string, nw: string) : Diff.Name =
        if old = nw then
            Diff.SameName(old)
        else
            Diff.Rename(old, nw)

    /// diff between two programs
    and prog (old: Program, nw: Program) : Diff.Program =
        let n = name (old.name, nw.name)
        let ds = decls (old.decls, nw.decls)
        { name = n; decls = ds }

    /// diff between two lists of declarations
    /// declarations of the same name are considered a changed declarations,
    /// all other declarations are consider adds/deletes, no renames are detected
    /// we assume order does not matter and diff them as sets
    and decls (old: Decl list, nw: Decl list) : Diff.DeclList = complexSet (old, nw, declSimilar, decl)

    /// checks if two declarations are similar
    and declSimilar (old: Decl, nw: Decl) =
        match old, nw with
        | Module (nO, dsO, _), Module (nN, dsN, _) -> nO = nN
        | Class (nO, tO, vsO, psO, msO, _), Class (nN, tN, vsN, psN, msN, _) -> nO = nN && tO = tN
        | Datatype (nO, tsO, csO, msO, _), Datatype (nN, tsN, csN, msN, _) -> nO = nN
        | ClassConstructor (nO, tsO, insO, outsO, bO, _), ClassConstructor (nN, tsN, insN, outsN, bN, _) -> nO = nN
        | Field (nO, tO, iO, gO, sO, mO, _), Field (nN, tN, iN, gN, sN, mN, _) ->
            nO = nN && gO = gN && sO = sN && mO = mN
        | Method (lO, nO, tsO, iO, oO, modO, readO, decrO, bO, gO, sO, qO, _),
          Method (lN, nN, tsN, iN, oN, modN, readN, decrN, bN, gN, sN, qN, _) ->
            nO = nN
            && lO = lN
            && gO = gN
            && sO = sN
            && qO = qN
        | TypeDef (nO, tsO, spO, prO, isNO, _), TypeDef (nN, tsN, spN, prN, isNN, _) ->
            isNO = isNN
            && (prO.IsNone && prN.IsNone
                || (prO.IsSome
                    && prN.IsSome
                    && (fst prO.Value) = (fst prN.Value)))
        | _ -> false

    /// diffs two similar declarations
    /// return None if not similar
    and decl (old: Decl, nw: Decl) : Diff.Decl option =
        match old, nw with
        | Module (nO, dsO, _), Module (nN, dsN, _) ->
            let n = name (nO, nN)
            let ds = decls (dsO, dsN)
            Some(Diff.Module(n, ds))
        | Class (nO, tO, vsO, psO, msO, _), Class (nN, tN, vsN, psN, msN, _) when tO = tN ->
            Some(Diff.Class(name (nO, nN), typeargs (vsO, vsN), classtypes (psO, psN), decls (msO, msN)))
        | Datatype (nO, tsO, csO, msO, _), Datatype (nN, tsN, csN, msN, _) ->
            Some(Diff.Datatype(name (nO, nN), typeargs (tsO, tsN), datatypeConstructors (csO, csN), decls (msO, msN)))
        | ClassConstructor (nO, tsO, insO, outsO, bO, _), ClassConstructor (nN, tsN, insN, outsN, bN, _) ->
            Some(
                Diff.ClassConstructor(
                    name (nO, nN),
                    typeargs (tsO, tsN),
                    inputSpec (insO, insN),
                    conditions (outsO, outsN),
                    exprO (bO, bN)
                )
            )
        | Field (nO, tO, iO, gO, sO, mO, _), Field (nN, tN, iN, gN, sN, mN, _) when gO = gN && sO = sN && mO = mN ->
            Some(Diff.Field(name (nO, nN), tp (tO, tN), exprO (iO, iN)))
        | Method (lO, nO, tsO, iO, oO, _, _, _, bO, gO, sO, qO, _),
          Method (lN, nN, tsN, iN, oN, modN, readN, decrN, bN, gN, sN, qN, _) when
            lO = lN && gO = gN && sO = sN && qO = qN ->
            Some(
                Diff.Method(name (nO, nN), typeargs (tsO, tsN), inputSpec (iO, iN), outputSpec (oO, oN), exprO (bO, bN))
            )
        | TypeDef (nO, tsO, spO, prO, isNO, _), TypeDef (nN, tsN, spN, prN, isNN, _) when
            // changing variable name (fst pr) not supported
            isNO = isNN
            && (prO.IsNone && prN.IsNone
                || (prO.IsSome
                    && prN.IsSome
                    && (fst prO.Value) = (fst prN.Value))) ->
            let s = Option.map snd
            Some(Diff.TypeDef(name (nO, nN), typeargs (tsO, tsN), tp (spO, spN), exprO (s prO, s prN)))
        | _ -> None

    /// diffs two sets of datatype constructors
    and datatypeConstructors (old: DatatypeConstructor list, nw: DatatypeConstructor list) =
        let similar (o: DatatypeConstructor, n: DatatypeConstructor) = o.name = n.name
        complexSet (old, nw, similar, (fun (o, n) -> Some(datatypeConstructor (o, n))))

    /// diffs two datatype constructors (not necessarily of the same name)
    and datatypeConstructor (old: DatatypeConstructor, nw: DatatypeConstructor) : Diff.DatatypeConstructor =
        Diff.DatatypeConstructor(name (old.name, nw.name), localDecls (old.ins, nw.ins))

    /// diffs two sets of class types (e.g., as occurring as parents of a class)
    /// We assume the order of class parents does not matter.
    and classtypes (old: ClassType list, nw: ClassType list) = simpleSet (old, nw)

    /// diffs two sets of conditions
    and conditions (old: Condition list, nw: Condition list) : Diff.ConditionList = simpleSet (old, nw)

    // common comment for the lists where order matters: typeargs and localdecls
    // Because these are subject to positional subsitution, handling reordering is very tricky.
    // Therefore, the list comparison methods are used, which spot insertions and deletions, but not reorderings.
    // Renamings are not spotted either.

    /// diffs two lists of type arguments
    /// insertions and deletions are detected, but renamings and reorderings generate Delete+Add
    and typeargs (old: TypeArg list, nw: TypeArg list) =
        let similar (o: TypeArg, n: TypeArg) = (fst o) = (fst n)
        complexList (old, nw, similar, (fun (o, n) -> Some(o))) // TODO: store both typeargs

    /// diffs two lists of local decls
    /// insertions and deletions are detected, but renamings and reorderings generate Delete+Add
    and localDecls (old: LocalDecl list, nw: LocalDecl list) =
        let similar (o: LocalDecl, n: LocalDecl) = o.name = n.name
        complexList (old, nw, similar, (fun (o, n) -> Some(localDecl (o, n))))

    // diffs two local declarations
    and localDecl (old: LocalDecl, nw: LocalDecl) =
        let n = name (old.name, nw.name)
        let t = tp (old.tp, nw.tp)
        Diff.LocalDecl(n, t)

    /// diffs two input specifications
    and inputSpec (old: InputSpec, nw: InputSpec) =
        match old, nw with
        | InputSpec (ldsO, reqsO), InputSpec (ldsN, reqsN) ->
            Diff.InputSpec(localDecls (ldsO, ldsN), conditions (reqsO, reqsN))

    /// diffs two output specifications
    and outputSpec (old: OutputSpec, nw: OutputSpec) =
        match old, nw with
        | OutputSpec (ldsO, reqsO), OutputSpec (ldsN, reqsN) ->
            Diff.OutputSpec(localDecls (ldsO, ldsN), conditions (reqsO, reqsN))

    /// diffs two optional expressions, no recursion: expressions are either equal or not
    and exprO (old: Expr option, nw: Expr option) =
        match old, nw with
        | None, None -> Diff.SameExprO old
        | Some o, Some n ->
            if o = n then
                Diff.SameExprO old
            else
                Diff.UpdateExpr n
        | Some o, None -> Diff.DeleteExpr o
        | None, Some n -> Diff.AddExpr n
    /// diffs two expressions
    and expr (old: Expr, nw: Expr) =
        if old = nw then
            Diff.SameExprO(Some old)
        else
            Diff.UpdateExpr nw
    /// diffs two types, no recursion: types are either equal or not
    and tp (old: Type, nw: Type) =
        if old = nw then
            Diff.SameType old
        else
            Diff.UpdateType nw
