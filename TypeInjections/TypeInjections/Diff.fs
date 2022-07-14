namespace TypeInjections

open System.Data.Common

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
        | UpdateList of Elem<'y, 'd> list
        member this.elements = match this with UpdateList l -> l
        /// true if all elements are unchanged
        member this.isSame = List.forall (fun (e: Elem<'y, 'd>) -> e.isSame) this.elements
        /// the unchanged elements
        member this.getSame = List.choose (fun e -> match e with Same y -> Some y | _ -> None) this.elements
        /// the added elements
        member this.getAdd = List.choose (fun e -> match e with Add y -> Some y | _ -> None) this.elements
        /// the deleted elements
        member this.getDelete = List.choose (fun e -> match e with Delete y -> Some y | _ -> None) this.elements

    /// change in an element of a list of YIL.y with comparision type Diff.d
    and Elem<'y, 'd> =
        | Same of 'y
        | Add of 'y
        | Delete of 'y
        | Update of 'y * 'd
        member this.isSame =
            match this with
            | Same _ -> true
            | _ -> false
        member this.yil =
            match this with
            | Same y
            | Add y
            | Delete y
            | Update (y,_) -> y

    type Name =
        | SameName of string
        | Rename of string * string

    and Program =
        { name: Name
          decls: List<Y.Decl, Decl> }

    and Decl =
        | Module of Name * DeclList
        | Class of Name * TypeArgList * ClassTypeList * DeclList
        | Datatype of Name * TypeArgList * DatatypeConstructorList * DeclList
        | ClassConstructor of Name * TypeArgList * InputSpec * ConditionList * ExprO
        | TypeDef of Name * TypeArgList * Type * ExprO
        | Field of Name * Type * ExprO
        | Method of Name * TypeArgList * InputSpec * OutputSpec * ExprO
        | Import of bool * YIL.Path
        | Export of YIL.Path list
        | DUnimplemented
        member this.name =
            match this with
            | Module(n,_) -> n
            | Class(n,_,_,_) -> n
            | Datatype(n,_,_,_) -> n
            | ClassConstructor(n,_,_,_,_) -> n
            | TypeDef(n,_,_,_) -> n
            | Field(n,_,_) -> n
            | Method(n,_,_,_,_) -> n
            // these should be impossible but it's more convenient to make the function total
            | DUnimplemented -> SameName "DUnimplemented"
            | Import _ -> SameName "IMPORT"
            | Export _ -> SameName "EXPORT"
            

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
        | InputSpec of LocalDeclList * ConditionList
        member this.decls = match this with | InputSpec(lds,_) -> lds
        member this.conditions = match this with | InputSpec(_,cs) -> cs
        member this.isSame = this.decls.isSame && this.conditions.isSame

    // change between output type and output decls is an add-delete
    and OutputSpec =
        | OutputSpec of LocalDeclList * ConditionList
        member this.decls = match this with | OutputSpec(lds,_) -> lds
        member this.conditions = match this with | OutputSpec(_,cs) -> cs
        member this.isSame = this.decls.isSame && this.conditions.isSame

    /// change to an optional expression
    and ExprO =
        | SameExprO of Y.Expr option // unchanged
        | AddExpr of Y.Expr
        | UpdateExpr of Y.Expr
        | DeleteExpr of Y.Expr
        member this.isSame = match this with SameExprO _ -> true | _ -> false

    /// change to a type
    and Type =
        | SameType of Y.Type
        | UpdateType of Y.Type
        member this.isSame = match this with SameType _ -> true | _ -> false

    // the identity diff of an object (occurrences of SameX are pushed one level down)
    let rec idDecl(d: YIL.Decl) =
        let nD = SameName d.name
        let tvsD = idList d.tpvars
        let msD = idList d.children
        match d with
        | YIL.DUnimplemented -> DUnimplemented
        | YIL.Export ps -> Export ps
        | YIL.Import(o, p) -> Import (o,p)
        | YIL.Module _ -> Module(nD, msD)
        | YIL.Datatype(_,_,ctrs,_,_) -> Datatype(nD,tvsD, idList ctrs, msD)
        | YIL.Class(_,_,_,ps,_,_) -> Class(nD, tvsD, idList ps, msD)
        | YIL.ClassConstructor(_,_,ins,outs,bd,_) -> ClassConstructor(nD,tvsD, idInputSpec ins, idList outs, SameExprO bd)
        | YIL.TypeDef(_,_,sp,pr,_,_) -> TypeDef(nD, tvsD, SameType sp, SameExprO (Option.map snd pr))
        | YIL.Field(_,t,d,_,_,_,_) -> Field(nD, SameType t, SameExprO d)
        | YIL.Method(_,_,_,ins,outs,bd,_,_,_) -> Method(nD, tvsD, idInputSpec ins, idOutputSpec outs, SameExprO bd)
    and idList<'y,'d>(ys: 'y list): List<'y,'d> = UpdateList(List.map Same ys)
    and idConstructor(ctr: YIL.DatatypeConstructor) = DatatypeConstructor(SameName ctr.name, idList ctr.ins)
    and idInputSpec(ins: YIL.InputSpec) = InputSpec(idList ins.decls, idList ins.conditions)
    and idOutputSpec(outs: YIL.OutputSpec) = OutputSpec(idList outs.decls, idList outs.conditions)
    and idLocalDecl(ld: YIL.LocalDecl) = LocalDecl(SameName ld.name, SameType ld.tp)

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
            | Update (_,y) -> UPD + " " + pd y

        member this.prog(p: Program) = this.decls p.decls

        member this.name(nm: Name) =
            match nm with
            | SameName o -> o
            | Rename (o, n) -> "(" + o + " -> " + n + ")"

        member this.typeargs(ts: TypeArgList) = this.List(ts, fst, fst, "<", ", ", ">")

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
            | Class (n, tpvs, cts, ds) ->
                (this.name n)
                + (this.typeargs tpvs)
                + this.classTypes cts
                + (this.decls ds)
            | ClassConstructor (n, tpvs, ins, outs, b) ->
                "constructor "
                + (this.name n)
                + (this.typeargs tpvs)
                + (this.inputSpec ins)
                + (this.conditions(false,outs))
                + " = \n"
                + this.exprO b
            | TypeDef(n,tvs,sp,pr) ->
                "type "
                + (this.name n)
                + " = "
                + (this.tp sp)
                + " | "
                + (this.exprO pr)
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
             | Import(o,p) -> P().decl(YIL.Import(o,p))
             | Export ps -> P().decl(YIL.Export ps)
             | DUnimplemented -> "Unimplemented"

        member this.datatypeConstructors(cs: DatatypeConstructorList) =
            this.List(cs, P().datatypeConstructor, this.datatypeConstructor, "", " | ", "")

        member this.datatypeConstructor(c: DatatypeConstructor) =
            match c with
            | DatatypeConstructor (n, ins) -> (this.name n) + (this.localDecls ins)

        member this.inputSpec(i: InputSpec) =
            match i with
            | InputSpec (lds, cs) ->
                this.localDecls lds
                + " "
                + this.conditions (true, cs)

        member this.outputSpec(s: OutputSpec) =
            match s with | OutputSpec (ds, cs) -> this.localDecls ds + " " + (this.conditions(false,cs))

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
            | SameExprO e -> UNC + (YIL.printer().exprO false (e, ""))
            | UpdateExpr e -> UPD + (YIL.printer().expr false e)
            | DeleteExpr _ -> DEL
            | AddExpr e -> ADD + (YIL.printer().expr false e)

        member this.localDecls(lds: LocalDeclList) =
            this.List(lds, P().localDecl, this.localDecl, "(", ", ", ")")

        member this.localDecl(ld: LocalDecl) =
            match ld with
            | LocalDecl (n, tO) -> (this.name n) + ": " + (this.tp tO)

        member this.classTypes(cts: ClassTypeList) =
            this.List(cts, P().classType, P().classType, "", ", ", "")
