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
