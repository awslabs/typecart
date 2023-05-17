namespace TypeInjections

open System
open System.IO
open System.Reflection
open TypeInjections.YIL

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
  
  /// recursively get rid of any path not in list of specified paths, in the AST.
  type RecursiveFilterTransform(mustPreserve: Path -> bool) =
      inherit Traverser.Identity()

      // internal nodes must be handled separately from leaf nodes.
      override this.decl(ctx: Context, decl: Decl) =
          let childCtx = ctx.enter decl.name
          if mustPreserve(ctx.currentDecl.child(decl.name)) then
              let decl' = this.declDefault(ctx, decl)
              decl' 
          else
              let pChildren =
                List.map (fun (childDecl: Decl) -> this.decl(childCtx, childDecl)) decl.children
                |> List.collect id
              match pChildren with
              | [] -> []
              | _ (* children preserved *) ->
                  let fDecl = decl.filterChildren(fun x -> List.contains x pChildren)
                  fDecl
          
              
      override this.prog(p: Program) =
          let p' = this.progDefault(p)
          p'
  
  /// Import joint, old, new in translations.
  type ImportInTranslationsModule() =
      inherit Traverser.Identity()
      
      override this.decl(ctx: Context, decl: Decl) =
          match decl with
          | Module(name, decls, meta) ->
              [ Module(name, Import (ImportDefault (Path ["Joint"]))
                               :: Import (ImportDefault (Path ["Old"]))
                               :: Import (ImportDefault (Path ["New"]))
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
              [ Module(name, Import (ImportDefault (Path ["Joint"]))
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
              match List.tryFind (fun p -> importPath.Equals(p)) ctx.importPaths with
              | Some _ -> true
              | None -> false
          match decl with
          | Module(name, decls, meta) ->
              let filtDecls =
                  List.map (fun decl ->
                      match decl with
                      | Import it ->
                          if importIn it then decl
                          else Import (it.prefix("Joint"))
                      | _ -> decl) decls
              [ Module(name, filtDecls, meta) ]
          | _ -> this.declDefault(ctx, decl)
      
      override this.prog(prog: Program) =
          let decls = prog.decls in
          let ctx =
              List.fold (fun (ctx: Context) decl ->
                  match decl with
                  | Module(name, _, _)-> ctx.addImport(ImportDefault (Path [name]))
                  | _ -> ctx) (Context(prog)) decls
          let dsT = List.collect (fun (d: Decl) -> this.decl (ctx, d)) prog.decls
          { name = prog.name
            decls = dsT
            meta = prog.meta }

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
        { name=prog.name; decls=List.map prD prog.decls; meta = prog.meta }
  
  /// Resolve module imports tagged along expressions and declarations.
  /// Dafny complains when we print out fully qualified names in some cases, hence this pass.
  type AnalyzeModuleImports() =
        inherit Traverser.Identity()
        
        // consume common prefix of current module path with current path.
        member this.consumeModulePath(p: Path, modulePath: Path) : Path =
            match p, modulePath with
            // We rename the old YIL AST to Joint AST, so the fully-qualified names don't include "Joint."
            // We don't do the same for translations module, since it is produced from scratch and the fully-qualified
            // names should include "Translations.".
            // Handle spcecial case first: when both paths are in the same module, then we elide both.
            | Path ("Joint" :: t1), Path ("Joint" :: t2) 
            | Path ("Translations" :: t1), Path ("Translations" :: t2)
            | Path ("New" :: t1), Path ("New" :: t2)
            | Path ("Old" :: t1), Path ("Old" :: t2) -> this.consumeModulePath(Path t1, Path t2)
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
        member this.consumeImportPath(p: Path) (import: ImportType) =
            match p, import with
            // Only consume common prefix of "import opened".
            // For instance, if the current module scope has "import Constant" and
            // the fully qualified path name is "Constant.int64", we should keep the
            // fully qualified path name here. However, if we "import opened Constant"
            // then the correct result should be Path ["int64"].
            | Path (a1 :: t1), ImportOpened (Path (a2 :: t2)) when a1.Equals(a2) ->
                this.consumeImportPath (Path(t1)) (ImportOpened (Path(t2)))
            | Path (a1 :: t1), ImportOpened (Path (a2 :: t2))
            | Path (a1 :: t1), ImportDefault (Path (a2 :: t2))
            | Path (a1 :: t1), ImportEquals (Path (a2 :: t2), _) -> p
            | _, _ -> p
            
        member this.doPath(p: Path, currModulePath: Path, imports: ImportType list) =
             let objectPath = this.consumeModulePath(p, currModulePath)
             let objectPath' = List.fold (this.consumeImportPath) objectPath imports
             objectPath'
        
        override this.receiver(ctx: Context, r: Receiver) =
            match r with
            | ObjectReceiver _ -> r // do not care about fields of e.g. local record vars.
            | StaticReceiver ct ->
                let imports = ctx.importPaths
                let currModulePath = ctx.modulePath()
                let objectPath = this.doPath(ct.path, currModulePath, imports)
                StaticReceiver {ct with path = objectPath}
        
        override this.tp(ctx: Context, t: Type) =
            let imports = ctx.importPaths
            let currModulePath = ctx.modulePath()
            let doPath p = this.doPath(p, currModulePath, imports)
            match t with
            | TApply (p, ts) -> TApply(doPath(p), List.map (fun x -> this.tp (ctx, x)) ts)
            | _ -> this.tpDefault(ctx, t)

     type DeduplicateImportsIncludes() =
         inherit Traverser.Identity()
         
         override this.prog(prog: Program) =
             let prog = this.progDefault(prog)
             let decls, _ = List.fold (fun (decls, includes: Path list) decl ->
                 match decl with
                 | Include p ->
                     match List.tryFind (fun x -> x.Equals(p)) includes with
                     | Some _ -> (decls, includes)
                     | None -> (decl :: decls, p :: includes)
                 | _ -> (decl :: decls, includes)) ([], []) prog.decls
             {prog with decls = List.rev decls}
         
         override this.decl(ctx: Context, d: Decl) =
             match d with
             | Module(name, decls, meta) ->
                   let newDecls, _ = List.fold (fun (newDecls: Decl list, paths: Path list) decl ->
                     match decl with
                     | Import it ->
                         match List.tryFind (fun x -> x.Equals(it.getPath())) paths with
                         | Some _ -> newDecls, paths
                         | None -> decl :: newDecls, it.getPath() :: paths
                     | _ -> decl :: newDecls, paths) ([], []) decls
                   [ Module (name, List.rev newDecls, meta) ]
             | _ -> this.declDefault(ctx, d) 
    
     type CreateEmptyModuleIfNoneExists(moduleName: string) =
         inherit Traverser.Identity()
         
         let noModule(t: Decl list) =
             match List.tryFind (function | Module _ -> true | _ -> false) t with
             | None -> true
             | Some _ -> false
         
         override this.prog(prog: Program) =
             match prog.decls with
             | [] as l | l when noModule(l) ->
                 {prog with decls = l @ [Module(moduleName, [], emptyMeta)]}
             | _ -> prog
    
    // MapBuiltinTypes.dfy, RelateBuiltinTypes.dfy
    type GenerateTranslationCode() =
        inherit Traverser.Identity()

        let retrieveResource (filename: string) : string =
            let asmb = Assembly.GetExecutingAssembly();
            // to check all assembly base names, use asmb.GetManifestResourceNames()
            let stream = asmb.GetManifestResourceStream($"TypeInjections.Resources.{filename}")
            let reader = new StreamReader(stream)
            reader.ReadToEnd()

        let relateBuiltinTypes = retrieveResource "RelateBuiltinTypes.dfy"
        let mapBuiltinTypes = retrieveResource "MapBuiltinTypes.dfy"
        
        override this.prog(prog: Program) =
            {prog with meta = {prog.meta with prelude = relateBuiltinTypes + "\n" + mapBuiltinTypes}}
            
    
    type Pipeline(passes : Traverser.Transform list) =
        member this.passes = passes
        member this.apply(prog: Program) =
            let rec oneRest (passes: (#Traverser.Transform) list) (r: Program) =
                match passes with
                | curr :: next ->
                    curr.prog(r) |> oneRest next
                | [] -> r
            oneRest this.passes prog

    
