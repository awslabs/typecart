namespace TypeInjections

/// AST for differences between two YIL programs
/// In particular, for every YIL AST type X that occurs in lists, the Diff AST has a type X with constructors
/// - AddX if the new list has a new element
/// - DeleteX if the new list misses an element
/// - C for every constructor C of X if an element was changed
/// The distinction between a change and a Delete+Add is not always clear,
/// but at least the kind and/or a name can be used to detect a change. 
module Diff =
    module Y = YIL
    module Utils = UtilsFR

    type Name = SameName of string | Rename of string*string
   
    and Program = {name: Name; decls: Decl list}
 
    and Decl =
        AddDecl of Y.Decl
      | DeleteDecl of string
      | Module of Name * Decl list
      | Class of Name * bool * TypeArg list * ClassType list * Decl list
      | Datatype of Name * TypeArg list * DatatypeConstructor list * Decl list
      | ClassConstructor of Name * TypeArg list * LocalDecl list * ExprO
      | Field of Name * Type * ExprO
      | Method of Name * TypeArg list * LocalDecl list * OutputSpec * ExprO
    
    and DatatypeConstructor =
        AddDatatypeConstructor of Y.DatatypeConstructor
      | DeleteDatatypeConstructor of string
      | DatatypeConstructor of Name * LocalDecl list
      
    and TypeArg =
      | AddTypeArg of string
      | DeleteTypeArg of string

    and ClassType =
      | AddClassType of Y.ClassType
      | DeleteClassType of Y.Path
    
    and LocalDecl =
        AddLocalDecl of Y.LocalDecl
      | DeleteLocalDecl of string
      | LocalDecl of Name * Type
    
    and OutputSpec =
      | SameOutputSpec // unchanged
      | UpdateToOutputType of Y.Type // was anything, now output type
      | UpdateToOutputDecls of Y.LocalDecl list // was output type, now decls
      | ChangeOutputDecls of LocalDecl list // was output decls, now different decls

    /// change to an optional expression
    and ExprO =
      | SameExprO // unchanged
      | AddExpr of Y.Expr // None ---> Some e
      | UpdateExpr of Y.Expr // Some e ---> Some e'
      | DeleteExpr // Some e -> None
        
    /// change to a type
    and Type =
      | SameType // unchanged
      | UpdateType of Y.Type // changed

    type Printer() =
        let mutable indentLevel = 0
        let indent () =
            Utils.listToString (List.map (fun _ -> "  ") [ 2 .. indentLevel ], "")
        let indented(s: string) = indent() + s + "\n"
        let withIndent(code: string Lazy) =
            indentLevel <- indentLevel + 1
            let s = code.Force()
            indentLevel <- indentLevel - 1
            s
        
        let ADD = "ADD "
        let DEL = "DEL "
        let UPD = "UPD"
        let UNC = "UNC"
        
        member this.prog(p: Program) = this.decls p.decls

        member this.name(nm: Name) =
            match nm with
            | SameName o -> o
            | Rename(o,n) -> "(" + o + " -> " + n + ")"
        
        member this.typeargs(ts: TypeArg list) =
            if ts.IsEmpty then
                ""
            else
                let s = List.map this.typearg ts
                "<" + Utils.listToString (s, ", ") + ">"

        member this.typearg(t: TypeArg) =
            match t with
            | AddTypeArg s -> ADD + s
            | DeleteTypeArg s -> DEL + s
        
        member this.decls(ds: Decl list) =
            withIndent(lazy
               Utils.listToString (List.map (fun d -> indented (this.decl d)) ds, "")
            )
        member this.decl(d: Decl) =
            match d with
            | AddDecl d -> ADD + YIL.printer().decl(d)
            | DeleteDecl n -> DEL + n
            | Module (n, ds) ->
                "module "
                + (this.name n)
                + "\n"
                + (this.decls ds)
            | Datatype (n, tpvs, cons, ds) ->
                let consS =
                    List.map this.datatypeConstructor cons
                "datatype "
                + (this.name n)
                + (this.typeargs tpvs)
                + " = "
                + Utils.listToString (consS, " | ")
                + "\n"
                + (this.decls ds)
            | Class (n, isTrait, tpvs, p, ds) ->
                if isTrait then "trait " else "class "
                + (this.name n)
                + (this.typeargs tpvs)
                + if p.IsEmpty then
                      ""
                  else
                      (" extends "
                       + Utils.listToString (List.map this.classType p, ",")
                       + " ")
                + " {\n"
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
                + (this.localDecls ins)
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

        member this.datatypeConstructor(c: DatatypeConstructor) =
            match c with
            | AddDatatypeConstructor c -> ADD + YIL.printer().datatypeConstructor c
            | DeleteDatatypeConstructor n -> DEL + n
            | DatatypeConstructor(n,ins) -> (this.name n) + (this.localDecls ins)
        
        member this.outputSpec(s: OutputSpec) =
            match s with
            | SameOutputSpec -> UNC
            | UpdateToOutputType t -> UPD + YIL.printer().tp(t)
            | UpdateToOutputDecls ds -> UPD + (YIL.printer().localDecls ds)
            | ChangeOutputDecls ds -> this.localDecls ds
        
        member this.tps(ts: Type list) =
            if ts.IsEmpty then
                ""
            else
                "<"
                + Utils.listToString (List.map this.tp ts, ",")
                + ">"

        member this.tp(tO: Type) =
            match tO with
            | SameType -> UNC
            | UpdateType t -> UPD + (t.ToString())

        member this.exprO(eO: ExprO) =
            match eO with
            | SameExprO -> UNC
            | UpdateExpr e -> UPD + (YIL.printer().expr e)
            | DeleteExpr -> DEL
            | AddExpr e -> ADD + (YIL.printer().expr e)
 
        member this.localDecls(lds: LocalDecl list) =
            "("
            + Utils.listToString (List.map this.localDecl lds, ", ")
            + ")"

        member this.localDecl(ld: LocalDecl) =
            match ld with
            | AddLocalDecl d -> ADD + YIL.printer().localDecl d
            | DeleteLocalDecl n -> DEL + n
            | LocalDecl(n,tO) -> (this.name n) + ": " + (this.tp tO)

        member this.classType(ct: ClassType) =
            match ct with
            | AddClassType c -> ADD + YIL.printer().classType(c)
            | DeleteClassType n -> DEL + n.ToString()

/// diffs two YIL AST items and returns the corresponding AST item in Diff._
module Differ =
    module Utils = UtilsFR
    open YIL
    
    /// diff between two names
    let rec name(old: string, nw: string): Diff.Name =
        if old = nw then Diff.SameName(old) else Diff.Rename(old,nw)
    
    /// diff between two programs
    and prog(old: Program, nw: Program): Diff.Program =
        let n = name(old.name,nw.name)
        let ds = decls(old.decls, nw.decls)
        {name = n; decls = ds}
        
    /// diff between two lists of declarations
    /// declarations of the same name are considered a changed declarations,
    /// all other declarations are consider adds/deletes, no renames are detected
    /// we assume order does not matter and diff them as sets
    and decls(old: Decl list, nw: Decl list): Diff.Decl list =
       let hasSameNameAs(d1: Decl)(d2: Decl) = d1.name = d2.name
       let diffOne(o: Decl) =
          match List.tryFind (hasSameNameAs o) nw with
          | Some n -> decl(o, n)
          | None -> [Diff.DeleteDecl(o.name)]
       let changed = List.collect diffOne old
       let added = List.filter (fun (n: Decl) -> not (List.exists (hasSameNameAs n) old)) nw
       changed @ (List.map Diff.AddDecl added)

    /// diffs two declarations (not necessarily of the same name or kind)
    /// tries to be smart but generates delete+add as default
    and decl(old: Decl, nw: Decl): Diff.Decl list =
        match old, nw with
        | o,n when o = n -> []
        | Module(nO,dsO,_), Module(nN,dsN,_) ->
           let n = name(nO,nN)
           let ds = decls(dsO, dsN)
           [Diff.Module(n, ds)]
        | Class(nO,tO,vsO,psO,msO,_), Class(nN,tN,vsN,psN,msN,_) when tO = tN ->
            [Diff.Class(
                name(nO,nN),
                tO,
                typeargs(vsO,vsN),
                classtypes(psO,psN),
                decls(msO,msN)
            )]
        | Datatype(nO, tsO, csO, msO, _), Datatype(nN, tsN, csN, msN, _) ->
            [Diff.Datatype(
                name(nO,nN),
                typeargs(tsO,tsN),
                datatypeConstructors(csO,csN),
                decls(msO,msN)
            )]
        | ClassConstructor(nO, tsO, insO, bO, _), ClassConstructor(nN, tsN, insN, bN, _) ->
            [Diff.ClassConstructor(
                name(nO,nN),
                typeargs(tsO,tsN),
                localDecls(insO,insN),
                exprO(bO,bN)
            )]
        | Field(nO, tO, iO, gO, sO, mO, _), Field(nN, tN, iN, gN, sN, mN, _) when gO = gN && sO = sN && mO = mN ->
            [Diff.Field(
                name(nO,nN),
                tp(tO,tN),
                exprO(iO,iN)
            )]
        | Method(nO,tsO,iO,oO,bO,gO,sO,_), Method(nN,tsN,iN,oN,bN,gN,sN,_) when gO = gN && sO = sN ->
            [Diff.Method(
                name(nO,nN),
                typeargs(tsO,tsN),
                localDecls(iO,iN),
                outputSpec(oO,oN),
                exprO(bO,bN)
            )]
        | _ -> [Diff.DeleteDecl(old.name); Diff.AddDecl(nw)]
    
    /// we assume order does not matter and diff them as sets
    and datatypeConstructors(old: DatatypeConstructor list, nw: DatatypeConstructor list) =
       let hasSameNameAs(d1: DatatypeConstructor)(d2: DatatypeConstructor) = d1.name = d2.name
       let diffOne(o: DatatypeConstructor) =
          match List.tryFind (hasSameNameAs o) nw with
          | Some n -> datatypeConstructor(o, n)
          | None -> [Diff.DeleteDatatypeConstructor(o.name)]
       let changed = List.collect diffOne old
       let added = List.filter (fun (n: DatatypeConstructor) -> not (List.exists (hasSameNameAs n) old)) nw
       changed @ (List.map Diff.AddDatatypeConstructor added)

    /// diffs two datatype constructors (not necessarily of the same name)
    and datatypeConstructor(old: DatatypeConstructor, nw: DatatypeConstructor) =
        if old = nw then
            []
        else
            [Diff.DatatypeConstructor(
                name(old.name, nw.name),
                localDecls(old.ins, nw.ins)
            )]

    /// diffs two lists of type arguments
    /// TODO this falsely assumes order does not matter and diffs them as sets
    and typeargs(old: string list, nw: string list) =
       List.map Diff.DeleteTypeArg (Utils.listDiff(old,nw)) @
       List.map Diff.AddTypeArg (Utils.listDiff(nw,old))
    
    /// diffs two lists of class types (e.g., as occurring as parents of a class)
    /// we assume order does not matter and diff them as sets
    and classtypes(old: ClassType list, nw: ClassType list) =
       List.map (fun ct -> Diff.DeleteClassType(ct.path)) (Utils.listDiff(old,nw)) @
       List.map Diff.AddClassType (Utils.listDiff(nw,old))

    /// diffs two lists of local decls
    /// insertions and deletions are detected, but renamings and reorderings generate Delete+Add
    and localDecls(old: LocalDecl list, nw: LocalDecl list) =
       let hasSameNameAs(d1: LocalDecl)(d2: LocalDecl) = d1.name = d2.name
       let mutable oldLeft = old
       let mutable newLeft = nw
       let mutable changes = []
       while not oldLeft.IsEmpty && not newLeft.IsEmpty do
           let o = oldLeft.Head
           oldLeft <- oldLeft.Tail
           if List.exists (hasSameNameAs o) newLeft then
             // same name exists later (possibly immediately next), assume everything in between is Add
             while o.name <> newLeft.Head.name do
                changes <- changes @ [Diff.AddLocalDecl(newLeft.Head)]
                newLeft <- newLeft.Tail
             // now o.name = n.name
             let n = newLeft.Head
             if o.tp <> n.tp then
               changes <- changes @ [Diff.LocalDecl(Diff.SameName o.name, Diff.UpdateType n.tp)]
              // else n = o, i.e., no change
             newLeft <- newLeft.Tail
           else
              // no declaration of this name anymore, assume Delete
              changes <- changes @ [Diff.DeleteLocalDecl o.name]
       // remaining old/new declarations become Delete/Add
       changes <- changes @
         (List.map (fun (d:LocalDecl) -> Diff.DeleteLocalDecl d.name) oldLeft) @ 
         (List.map Diff.AddLocalDecl newLeft)
       changes
       
    /// diffs two output specifications
    and outputSpec(old: OutputSpec, nw: OutputSpec) =
        match old, nw with
        | o,n when o = n ->
            Diff.SameOutputSpec
        | _, OutputType n ->
            Diff.UpdateToOutputType n
        | OutputType _, OutputDecls n ->
            Diff.UpdateToOutputDecls n
        | OutputDecls o, OutputDecls n ->
            Diff.ChangeOutputDecls(localDecls(o,n))
       
    /// diffs two expressions, no recursion: expressions are either equal or not
    and expr(old: Expr, nw: Expr) =
        if old = nw then
            None
        else
            Some nw

    /// diffs two optional expressions, no recursion: expressions are either equal or not     
    and exprO(old: Expr option, nw: Expr option) =
        match old,nw with
        | None, None -> Diff.SameExprO
        | Some o, Some n -> if o = n then Diff.SameExprO else Diff.UpdateExpr n
        | Some _, None -> Diff.DeleteExpr
        | None, Some n -> Diff.AddExpr n

    /// diffs two types, no recursion: types are either equal or not
    and tp(old: Type, nw: Type) =
        if old = nw then
            Diff.SameType
        else
            Diff.UpdateType nw

