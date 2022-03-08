namespace TypeInjections

open TypeInjections.YIL

/// AST for differences between two YIL programs
module Diff =
    module Y = YIL
    
    type Name = (string*string) option
   
    and Program = {name: Name; decls: Decl list}
 
    and Decl =
        AddDecl of Y.Decl
      | DeleteDecl of string
      | Module of Name * Decl list
      | Class of Name * TypeArg list * ClassType list * Decl list
      | Datatype of Name * TypeArg list * DatatypeConstructor list * Decl list
      | ClassConstructor of Name * TypeArg list * LocalDecl list * ExprO
      | Field of Name * Type * ExprO
      | Method of Name * TypeArg list * LocalDecl list * OutputSpec option * ExprO
    
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
      | LocalDecl of Name * Y.Type option
    
    and OutputSpec =
      | UpdateToOutputType of Y.Type // was anything, now output type
      | UpdateToOutputDecls of Y.LocalDecl list // was output type, now decls
      | ChangeOutputDecls of LocalDecl list // was output decls, now different decls

    and ExprO = Y.Expr option option
    
    and Type = Y.Type option

/// diffs two YIL AST items and returns the corresponding AST item in Diff._
module Differ =
    module D = Diff
    module Utils = UtilsFR
    
    /// diff between two names
    let rec name(old: string, nw: string): Diff.Name =
        if old = nw then None else Some(old,nw)
    
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
               changes <- changes @ [Diff.LocalDecl(None, Some n.tp)]
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
        | o,n when o = n -> None
        | _, OutputType n ->
            Some (Diff.UpdateToOutputType n)
        | OutputType _, OutputDecls n ->
            Some (Diff.UpdateToOutputDecls n)
        | OutputDecls o, OutputDecls n ->
            Some (Diff.ChangeOutputDecls(localDecls(o,n)))
       
    /// diffs two expressions, no recursion: expressions are either equal or not
    and expr(old: Expr, nw: Expr) =
        if old = nw then
            None
        else
            Some nw

    /// diffs two optional expressions        
    and exprO(old: Expr option, nw: Expr option) =
        if old = nw then
            None
        else
            Some nw

    /// diffs two types, no recursion: expressions are either equal or not
    and tp(old: Type, nw: Type) =
        if old = nw then
            None
        else
            Some nw

