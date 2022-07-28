namespace TypeInjections

open YIL

module Analysis =
  /// dependency of two declarations
  /// DepSpec: used in specification but not body
  /// DepComp: used in specification and/or body
  type Dependency =
      | DepNone | DepSpec | DepComp
      /// DepNone < DepSpec < DepComp
      member this.union(that: Dependency) =
          match this,that with
          | DepComp,_ | _,DepComp -> DepComp
          | DepSpec,_ | _,DepSpec -> DepSpec
          | _ -> DepNone

  /// helper class of usedBy
  type UsedByTraverser(p: Path) =
      inherit Traverser.Identity()
      let mutable dep = DepNone
      member this.getDep() = dep
      override this.path(ctx: Context, q:Path) =
          if p.isAncestorOf(q) then
             let d = if ctx.pos = BodyPosition then DepComp else DepSpec
             dep <- dep.union(d)
          q
  /// returns info on if/how p is used in d
  let usedBy(ctx: Context, p: Path, d: Decl): Dependency =
      let c = UsedByTraverser(p)
      c.decl(ctx, d) |> ignore
      c.getDep()
  
  /// for a list 'ds' of declarations making up the body of the current declaration,
  /// return the dependency closure of a subset 'start' of those declarations (reflexive, transitive) 
  let dependencyClosure(ctx: Context, ds: Decl list, start: Path list) =
      let mutable closure: Path list = []
      let rec add(p: Path) =
         closure <- p :: closure
         // recurse for every declaration not already in the closure and used by p
         List.iter (fun (d:Decl) ->
             let dp = ctx.currentDecl.child(d.name)
             if not (List.contains dp closure) && usedBy(ctx, p, d) <> DepNone then
                add(dp)
             ) ds
      List.iter add start
      closure
 
  /// Import joint, old, new in combine.
  type ImportInCombine() =
      inherit Traverser.Identity()
      
      override this.decl(ctx: Context, decl: Decl) =
          match decl with
          | Module(name, decls, meta) ->
              [ Module(name, Import(false, Path ["Joint"])
                               :: Import(false, Path ["Old"])
                               :: Import(false, Path ["New"])
                               :: decls, meta) ]
          | _ -> this.declDefault(ctx, decl)
      
      override this.prog(prog: Program) =
          let prog' = this.progDefault(prog)
          { prog' with decls = (Include(Path ["joint.dfy"]))
                               :: (Include (Path ["old.dfy"]))
                               :: (Include (Path ["new.dfy"]))
                               :: prog'.decls }
  
  type ImportJointInOldNew() =
      inherit Traverser.Identity()
      
      override this.decl(ctx: Context, decl: Decl) =
          match decl with
          | Module(name, decls, meta) ->
              [ Module(name, Import(false, Path ["Joint"])
                               :: decls, meta) ]
          | _ -> this.declDefault(ctx, decl)
      
      override this.prog(prog: Program) =
          let prog' = this.progDefault(prog)
          { prog' with decls = (Include(Path ["joint.dfy"]))
                               :: prog'.decls }
  
  /// Any import that isn't found in the old, new ASTs must belong in Joint module.
  type PrefixNotFoundImportsWithJoint() =
      inherit Traverser.Identity()
      
      override this.decl(ctx: Context, decl: Decl) =
          let importIn importPath =
              match List.tryFind (fun (p, _) -> p.Equals(importPath)) ctx.importPaths with
              | Some _ -> true
              | None -> false
          match decl with
          | Module(name, decls, meta) ->
              let filtDecls =
                  List.map (fun decl ->
                      match decl with
                      | Import (o, p) ->
                          if importIn p then decl
                          else Import (o, p.prefix("Joint"))
                      | _ -> decl) decls
              [ Module(name, filtDecls, meta) ]
          | _ -> this.declDefault(ctx, decl)
      
      override this.prog(prog: Program) =
          let decls = prog.decls in
          let ctx =
              List.fold (fun (ctx: Context) decl ->
                  match decl with
                  | Module(name, _, _)-> ctx.addImport(Path [name], ImportDefault)
                  | _ -> ctx) (Context(prog)) decls
          let dsT = List.collect (fun (d: Decl) -> this.decl (ctx, d)) prog.decls
          { name = prog.name
            decls = dsT }

  /// Prefixes the names of all toplevel modules
  type PrefixTopDecls(pref: string) =
    inherit Traverser.Identity()
    member this.pref = pref
    
      override this.prog(prog: Program) =
        let prN (n: string) = pref + "." + n
        let prD (d: YIL.Decl) =
            match d with
            | YIL.Module(n,ds,mt) -> YIL.Module(prN n, ds, mt)
            | d -> d
        {name=prog.name; decls=List.map prD prog.decls}
  
  /// Resolve module imports tagged along expressions and declarations.
  /// Dafny complains when we print out fully qualified names in some cases, hence this pass.
  type AnalyzeModuleImports() =
        inherit Traverser.Identity()
        
        // consume common prefix of current module path with current path.
        member this.consumeModulePath(p: Path, modulePath: Path) =
            match p, modulePath with
            // We rename the old YIL AST to Joint AST, so the fully-qualified names don't include "Joint."
            // We don't do the same for combine, since it is produced from scratch and the fully-qualified
            // names should include "Combine.".
            | _, Path ("Joint" :: t) -> this.consumeModulePath(p, Path(t))
            | _, Path ("New" :: t) -> this.consumeModulePath(p, Path(t))
            | _, Path ("Old" :: t) -> this.consumeModulePath(p, Path(t))
            // remove common prefix of current module scope and the fully qualified path "p".
            // For instance, if current module scope is CommonTypes.Option and p = Path [CommonTypes, Option, None]
            // then the result should be Path [None]
            | Path (a1 :: t1), Path (a2 :: t2) ->
                if a1.Equals(a2) then this.consumeModulePath(Path(t1), Path(t2))
                else p
            | _, _ -> p

        // consume common prefix of an import path with current path.
        member this.consumeImportPath(p: Path) (import: (Path * ImportType)) =
            let importPath, importType = import
            match p, importPath with
            // Only consume common prefix of "import opened".
            // For instance, if the current module scope has "import Constant" and
            // the fully qualified path name is "Constant.int64", we should keep the
            // fully qualified path name here. However, if we "import opened Constant"
            // then the correct result should be Path ["int64"].
            | Path (a1 :: t1), Path (a2 :: t2) ->
                if a1.Equals(a2) && (importType = ImportOpened) then
                    this.consumeImportPath (Path(t1)) (Path(t2), ImportOpened)
                else
                    p
            | _, _ -> p
        
        
        override this.receiver(ctx: Context, r: Receiver) =
            match r with
            | ObjectReceiver _ -> r // do not care about fields of e.g. local record vars.
            | StaticReceiver ct ->
                let imports = ctx.importPaths
                let currModulePath = ctx.modulePath
                let objectPath = this.consumeModulePath(ct.path, currModulePath)
                let objectPath = List.fold (this.consumeImportPath) objectPath imports
                StaticReceiver {ct with path = objectPath}

     type DeduplicateImports() =
         inherit Traverser.Identity()
         
         override this.decl(ctx: Context, d: Decl) =
             match d with
             | Module(name, decls, meta) ->
                   let newDecls, _ = List.fold (fun (newDecls: Decl list, paths: Path list) decl ->
                     match decl with
                     | Import (_, p) ->
                         match List.tryFind (fun x -> x.Equals(p)) paths with
                         | Some _ -> newDecls, paths
                         | None -> decl :: newDecls, p :: paths
                     | _ -> decl :: newDecls, paths) ([], []) decls
                   [ Module (name, List.rev newDecls, meta) ]
             | _ -> this.declDefault(ctx, d) 
     
    
     type Filter(declFilter: Decl -> bool) =
        inherit Traverser.Identity()
        member this.declFilter = declFilter
        override this.prog(prog: Program) =
             {YIL.name = prog.name; YIL.decls = List.filter this.declFilter prog.decls}


    type Pipeline(passes : Traverser.Transform list) =
        member this.passes = passes
        member this.apply(prog: Program) =
            let rec oneRest (passes: (#Traverser.Transform) list) (r: Program) =
                match passes with
                | curr :: next ->
                    curr.prog(r) |> oneRest next
                | [] -> r
            oneRest this.passes prog

    let mkFilter(only: string -> bool) = Filter(fun (d: Decl) -> only d.name)
