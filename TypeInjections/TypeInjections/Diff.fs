namespace TypeInjections

// variable naming conventions:
//  old or o: the old version
//  nw or n: the new version
//  if old/nw lists, then o/n for elements
//  'y for a YIL type
//  'd for the corresponding Diff type

/// AST for differences between two YIL programs
/// In particular, for every YIL AST type X that occurs in lists, the Diff AST has a type X with constructors
/// - AddX if the new list has a new element
/// - DeleteX if the new list misses an element
/// - C for every constructor C of X if an element was changed
/// The distinction between a change and a Delete+Add is not always clear,
/// but at least the kind and/or a name can be used to detect a change.
module Diff =
    module Y = YIL

    /// change in a list of YIL.y elements with comparison type Diff.d
    type List<'y, 'd> =
        | SameList of 'y list
        | UpdateList of Elem<'y, 'd> list
        member this.isSame =
            match this with
            | SameList _ -> true
            | UpdateList l -> List.forall (fun (e: Elem<'y, 'd>) -> e.isSame) l

    /// change in an element of a list of YIL.y with comparision type Diff.d
    and Elem<'y, 'd> =
        | Same of 'y
        | Add of 'y
        | Delete of 'y
        | Update of 'd
        member this.isSame =
            match this with
            | Same _ -> true
            | _ -> false

    type Name =
        | SameName of string
        | Rename of string * string

    and Program =
        { name: Name
          decls: List<Y.Decl, Decl> }

    and Decl =
        | Module of Name * DeclList
        | Class of Name * bool * TypeArgList * ClassTypeList * DeclList
        | Datatype of Name * TypeArgList * DatatypeConstructorList * DeclList
        | ClassConstructor of Name * TypeArgList * LocalDeclList * ExprO
        | Field of Name * Type * ExprO
        | Method of Name * TypeArgList * InputSpec * OutputSpec * ExprO

    and DeclList = List<Y.Decl, Decl>

    and DatatypeConstructor = DatatypeConstructor of Name * LocalDeclList

    and DatatypeConstructorList = List<Y.DatatypeConstructor, DatatypeConstructor>

    and TypeArg = Y.TypeArg

    and TypeArgList = List<Y.TypeArg, TypeArg>

    and ClassType = Y.ClassType

    and ClassTypeList = List<Y.ClassType, ClassType>

    and LocalDecl = LocalDecl of Name * Type

    and LocalDeclList = List<Y.LocalDecl, LocalDecl>

    and Condition = Y.Condition

    and ConditionList = List<Y.Condition, Condition>

    and InputSpec =
        | SameInputSpec of Y.InputSpec
        | InputSpec of LocalDeclList * ConditionList

    and OutputSpec =
        | SameOutputSpec of Y.OutputSpec
        | UpdateToOutputType of Y.Type * ConditionList
        | UpdateToOutputDecls of Y.LocalDecl list * ConditionList // was output type, now decls
        | ChangeOutputDecls of LocalDeclList * ConditionList // was output decls, now different decls

    /// change to an optional expression
    and ExprO =
        | SameExprO of Y.Expr option // unchanged
        | AddExpr of Y.Expr
        | UpdateExpr of Y.Expr
        | DeleteExpr of Y.Expr

    /// change to a type
    and Type =
        | SameType of Y.Type
        | UpdateType of Y.Type

    type Printer() =
        let mutable indentLevel = 0

        let indent () =
            Utils.listToString (List.map (fun _ -> "  ") [ 2 .. indentLevel ], "")

        let indented (s: string) = indent () + s + "\n"

        let withIndent (code: string Lazy) =
            indentLevel <- indentLevel + 1
            let s = code.Force()
            indentLevel <- indentLevel - 1
            s

        /// prefix for added elements
        let ADD = "ADD "
        /// prefix for deleted elements
        let DEL = "DEL "
        /// prefix for changed elements
        let UPD = "UPD"
        /// prefix for unchanged elements
        let UNC = "UNC"

        /// a YIL printer
        let P () = YIL.printer ()

        /// prints a diff between two lists, given printing functions for the YIL and Diff types
        member this.List<'y, 'd>
            (
                l: List<'y, 'd>,
                py: 'y -> string,
                pd: 'd -> string,
                bef: string,
                sep: string,
                aft: string
            ) =
            match l with
            | SameList y ->
                UNC
                + " "
                + bef
                + Utils.listToString (List.map py y, sep)
                + aft
            | UpdateList es ->
                bef
                + Utils.listToString (List.map (fun e -> this.Elem(e, py, pd)) es, sep)
                + aft

        /// prints an element of a diff between two lists, see also this.List
        member this.Elem<'y, 'd>(e: Elem<'y, 'd>, py: 'y -> string, pd: 'd -> string) =
            match e with
            | Same y -> UNC + " " + py y
            | Add y -> ADD + " " + py y
            | Delete y -> DEL + " " + py y
            | Update y -> UPD + " " + pd y

        member this.prog(p: Program) = this.decls p.decls

        member this.name(nm: Name) =
            match nm with
            | SameName o -> o
            | Rename (o, n) -> "(" + o + " -> " + n + ")"

        member this.typeargs(ts: TypeArgList) = this.List(ts, id, id, "<", ", ", ">")

        member this.decls(ds: DeclList) =
            this.List(ds, P().decl, this.decl, "{\n", "\n", "\n}")

        member this.decl(d: Decl) =
            match d with
            | Module (n, ds) -> "module " + (this.name n) + "\n" + (this.decls ds)
            | Datatype (n, tpvs, cons, ds) ->
                "datatype "
                + (this.name n)
                + (this.typeargs tpvs)
                + " = "
                + this.datatypeConstructors cons
                + "\n"
                + (this.decls ds)
            | Class (n, isTrait, tpvs, cts, ds) ->
                if isTrait then "trait " else "class "
                + (this.name n)
                + (this.typeargs tpvs)
                + this.classTypes cts
                + (this.decls ds)
            | Field (n, t, e) ->
                "field "
                + (this.name n)
                + ": "
                + (this.tp t)
                + " = "
                + this.exprO e
            | Method (n, tpvs, ins, outs, b) ->
                "method "
                + (this.name n)
                + (this.typeargs tpvs)
                + (this.inputSpec ins)
                + ": "
                + (this.outputSpec outs)
                + " = \n"
                + this.exprO b
            | ClassConstructor (n, tpvs, ins, b) ->
                "constructor "
                + (this.name n)
                + (this.typeargs tpvs)
                + (this.localDecls ins)
                + " = \n"
                + this.exprO b

        member this.datatypeConstructors(cs: DatatypeConstructorList) =
            this.List(cs, P().datatypeConstructor, this.datatypeConstructor, "", " | ", "")

        member this.datatypeConstructor(c: DatatypeConstructor) =
            match c with
            | DatatypeConstructor (n, ins) -> (this.name n) + (this.localDecls ins)

        member this.inputSpec(i: InputSpec) =
            match i with
            | SameInputSpec i -> UNC + (YIL.printer().inputSpec i)
            | InputSpec (lds, cs) ->
                this.localDecls lds
                + " "
                + this.conditions (true, cs)

        member this.outputSpec(s: OutputSpec) =
            match s with
            | SameOutputSpec os -> UNC + (YIL.printer().outputSpec os)
            | UpdateToOutputType (t, _) -> UPD + YIL.printer().tp (t)
            | UpdateToOutputDecls (ds, _) -> UPD + (YIL.printer().localDecls ds)
            | ChangeOutputDecls (ds, _) -> this.localDecls ds

        member this.conditions(require: bool, cDs: ConditionList) =
            let p = (fun c -> P().condition (require, c))
            this.List(cDs, p, p, "", ", ", "")

        member this.tps(ts: Type list) =
            if ts.IsEmpty then
                ""
            else
                "<"
                + Utils.listToString (List.map this.tp ts, ",")
                + ">"

        member this.tp(tO: Type) =
            match tO with
            | SameType t -> UNC + (t.ToString())
            | UpdateType t -> UPD + (t.ToString())

        member this.exprO(eO: ExprO) =
            match eO with
            | SameExprO e -> UNC + (YIL.printer().exprO (e, ""))
            | UpdateExpr e -> UPD + (YIL.printer().expr e)
            | DeleteExpr _ -> DEL
            | AddExpr e -> ADD + (YIL.printer().expr e)

        member this.localDecls(lds: LocalDeclList) =
            this.List(lds, P().localDecl, this.localDecl, "(", ", ", ")")

        member this.localDecl(ld: LocalDecl) =
            match ld with
            | LocalDecl (n, tO) -> (this.name n) + ": " + (this.tp tO)

        member this.classTypes(cts: ClassTypeList) =
            this.List(cts, P().classType, P().classType, "", ", ", "")

/// diffs two YIL AST items and returns the corresponding AST item in Diff._
module Differ =
    open YIL

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
                    Diff.Update d
                | None -> Diff.Delete o

        let changed = List.map diffOne old
        // append Add for the elements of nw that have not been used by diffOne
        let diff =
            changed
            @ (List.map Diff.Add (Utils.listDiff (nw, nwDiffed)))

        let d = Diff.UpdateList(diff)
        // check if all elements are the same
        if d.isSame then
            Diff.SameList old
        else
            d

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
            if not nwLeft.IsEmpty then
                // old delcarations deleted at the end
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
                    let d = Option.get (diff (o, n)) // succeeds by precondition
                    // now o = n
                    (List.map Diff.Add added) @ [ Diff.Update d ]
                | None ->
                    // no similar elements occurs later, assume deleted
                    [ Diff.Delete o ]

        let changed = List.collect diffOne old
        // append new additions at the end
        let diff = changed @ List.map Diff.Add nwLeft
        let d = Diff.UpdateList(diff)
        // check if all elements were the same
        if d.isSame then
            Diff.SameList old
        else
            d

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
        | ClassConstructor (nO, tsO, insO, bO, _), ClassConstructor (nN, tsN, insN, bN, _) -> nO = nN
        | Field (nO, tO, iO, gO, sO, mO, _), Field (nN, tN, iN, gN, sN, mN, _) ->
            nO = nN && gO = gN && sO = sN && mO = mN
        | Method (lO, nO, tsO, iO, oO, bO, gO, sO, _), Method (lN, nN, tsN, iN, oN, bN, gN, sN, _) ->
            nO = nN && lO = lN && gO = gN && sO = sN
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
            Some(Diff.Class(name (nO, nN), tO, typeargs (vsO, vsN), classtypes (psO, psN), decls (msO, msN)))
        | Datatype (nO, tsO, csO, msO, _), Datatype (nN, tsN, csN, msN, _) ->
            Some(Diff.Datatype(name (nO, nN), typeargs (tsO, tsN), datatypeConstructors (csO, csN), decls (msO, msN)))
        | ClassConstructor (nO, tsO, insO, bO, _), ClassConstructor (nN, tsN, insN, bN, _) ->
            Some(Diff.ClassConstructor(name (nO, nN), typeargs (tsO, tsN), localDecls (insO, insN), exprO (bO, bN)))
        | Field (nO, tO, iO, gO, sO, mO, _), Field (nN, tN, iN, gN, sN, mN, _) when gO = gN && sO = sN && mO = mN ->
            Some(Diff.Field(name (nO, nN), tp (tO, tN), exprO (iO, iN)))
        | Method (lO, nO, tsO, iO, oO, bO, gO, sO, _), Method (lN, nN, tsN, iN, oN, bN, gN, sN, _) when
            lO = lN && gO = gN && sO = sN ->
            Some(
                Diff.Method(name (nO, nN), typeargs (tsO, tsN), inputSpec (iO, iN), outputSpec (oO, oN), exprO (bO, bN))
            )
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
    and typeargs (old: TypeArg list, nw: TypeArg list) = simpleList (old, nw)

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
        | o, n when o = n -> Diff.SameInputSpec o
        | InputSpec (ldsO, reqsO), InputSpec (ldsN, reqsN) ->
            Diff.InputSpec(localDecls (ldsO, ldsN), conditions (reqsO, reqsN))

    /// diffs two output specifications
    and outputSpec (old: OutputSpec, nw: OutputSpec) =
        let cs =
            conditions (old.conditions, nw.conditions)

        match old, nw with
        | o, n when o = n -> Diff.SameOutputSpec o
        | _, OutputType (n, _) -> Diff.UpdateToOutputType(n, cs)
        | OutputType _, OutputDecls (n, _) -> Diff.UpdateToOutputDecls(n, cs)
        | OutputDecls (o, _), OutputDecls (n, _) -> Diff.ChangeOutputDecls(localDecls (o, n), cs)

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

    /// diffs two types, no recursion: types are either equal or not
    and tp (old: Type, nw: Type) =
        if old = nw then
            Diff.SameType old
        else
            Diff.UpdateType nw
