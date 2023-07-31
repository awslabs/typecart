namespace TypeInjections

open System
open System.Drawing
open System.IO
open System.Reflection
open TypeInjections.YIL

module Analysis =
    /// dependency of two declarations
    /// DepSpec: used in specification but not body
    /// DepComp: used in specification and/or body
    type Dependency =
        | DepNone
        | DepSpec
        | DepComp
        /// DepNone < DepSpec < DepComp
        member this.union(that: Dependency) =
            match this, that with
            | DepComp, _
            | _, DepComp -> DepComp
            | DepSpec, _
            | _, DepSpec -> DepSpec
            | _ -> DepNone

    /// helper class of usedBy
    type UsedByTraverser(p: Path) =
        inherit Traverser.Identity()
        let mutable dep = DepNone
        member this.getDep() = dep

        override this.path(ctx: Context, q: Path) =
            if p.isAncestorOf (q) then
                let d =
                    if ctx.pos = BodyPosition then
                        DepComp
                    else
                        DepSpec

                dep <- dep.union (d)

            q
    /// returns info on if/how p is used in d
    let usedBy (ctx: Context, p: Path, d: Decl) : Dependency =
        let c = UsedByTraverser(p)
        c.decl (ctx, d) |> ignore
        c.getDep ()

    /// for a list 'ds' of declarations making up the body of the current declaration,
    /// return the dependency closure of a subset 'start' of those declarations (reflexive, transitive)
    let dependencyClosure (ctx: Context, ds: Decl list, start: Path list) =
        let mutable closure : Path list = []

        let rec add (p: Path) =
            closure <- p :: closure
            // recurse for every declaration not already in the closure and used by p
            List.iter
                (fun (d: Decl) ->
                    let dp = ctx.currentDecl.child (d.name)

                    if not (List.contains dp closure)
                       && usedBy (ctx, p, d) <> DepNone then
                        add (dp))
                ds

        List.iter add start
        closure

    /// filters declarations by applying a predicate to their path
    type FilterDecls(keep: Path -> bool) =
        inherit Traverser.Identity()
        override this.ToString() = "filtering declarations"

        override this.decl(ctx: Context, decl: Decl) =
            let childCtx = ctx.enter decl.name
            let preservedChildren (d: Decl) = keep (ctx.currentDecl.child (d.name))
            let declsF = decl.filterChildren preservedChildren
            this.declDefault (childCtx, declsF)

        override this.prog(p: Program) =
            let dsF =
                p.decls
                |> List.filter (fun (d: Decl) -> keep (Path [ d.name ]))

            let pF = { p with decls = dsF }
            pF // this.progDefault(pF)

    /// add certain includes to a program and certain imports to every module
    type AddImports(incls: string list, imps: string list) =
        inherit Traverser.Identity()

        override this.ToString() =
            "adding imports of "
            + (Utils.listToString (imps, ", "))

        override this.prog(prog: Program) =
            let prog' = this.progDefault (prog)

            let is =
                incls |> List.map (fun i -> Include(Path [ i ]))

            { prog' with decls = is @ prog'.decls }

        override this.decl(ctx: Context, decl: Decl) =
            match decl with
            | Module (name, decls, meta) ->
                let is =
                    imps
                    |> List.map (fun i -> Import(ImportDefault(false, Path [ i ])))
                // We may also need to add imports to submodules.
                this.declDefault (ctx, Module(name, is @ decls, meta))
            | _ -> this.declDefault (ctx, decl)

    type GatherAllModules() =
        inherit Traverser.Identity()
        
        let mutable result: Set<ImportType> = Set.empty
        
        override this.decl(ctx: Context, d: Decl) : Decl list =
            match d with
            | Module (name, _, _) ->
                result <- result.Add(ImportDefault(false, Path [ name ]))
            | _ -> ()
            this.declDefault(ctx, d)
        
        member this.gather (prog: Program) =
            this.progDefault(prog) |> ignore
            result

    /// adds a given prefix to every import not found in the current AST;
    /// note that a module with an extra prefix in the current AST is considered as found
    type PrefixUnfoundImports(prefix: string) =
        inherit Traverser.Identity()

        override this.ToString() =
            "prefixing unfound imports with " + prefix

        override this.decl(ctx: Context, decl: Decl) =
            let importIn importPath =
                match List.tryFind (fun p -> importPath.Equals(p)) ctx.importPaths with
                | Some _ -> true
                | None -> false

            let importDifferByPrefix (importPath: ImportType) =
                match List.tryFind
                          (fun (p: ImportType) ->
                              importPath
                                  .getPath()
                                  .onlyDifferByPrefix (p.getPath ()))
                          ctx.importPaths with
                | Some p -> p.getPath().names[0].Split(".")[0]  // the prefix
                | None -> ""

            match decl with
            | Module (name, decls, meta) ->
                let filtDecls =
                    List.map
                        (fun decl ->
                            match decl with
                            | Import it ->
                                if importIn it then
                                    decl
                                else
                                    let existingPrefix = importDifferByPrefix it
                                    if existingPrefix <> "" && existingPrefix <> prefix then
                                        decl  // do not prefix it
                                    else
                                        Import(it.prefix prefix)
                            | _ -> decl)
                        decls

                // Prefix unfound imports in nested modules
                this.declDefault (ctx, Module(name, filtDecls, meta))
            | _ -> this.declDefault (ctx, decl)

        override this.prog(prog: Program) =
            let modules = GatherAllModules().gather(prog)
            let ctx = Set.fold (fun (ctx: Context) import -> ctx.addImport(import)) (Context(prog)) modules

            let dsT =
                List.collect (fun (d: Decl) -> this.decl (ctx, d)) prog.decls

            { name = prog.name
              decls = dsT
              meta = prog.meta }

    /// prefixes the names of all toplevel modules in a program (only to be called on programs)
    type PrefixTopDecls(pref: string) =
        inherit Traverser.Identity()
        override this.ToString() = "prefixing toplevel decls with " + pref

        override this.prog(prog: Program) =
            let prN (n: string) = pref + "." + n

            let prD (d: Decl) =
                match d with
                | Module (n, ds, mt) -> Module(prN n, ds, mt)
                | d -> d

            { name = prog.name
              decls = List.map prD prog.decls
              meta = prog.meta }
    
    /// Returns a map from each path to all children in it (but not in nested modules or in datatypes)
    type GatherAllPaths() =
        inherit Traverser.Identity()
        
        // Datatype constructors have lower priorities than local names.
        //
        // Phase 0: Add datatype constructor names to the modules. We can use C directly in A if A.B.C is a datatype
        // constructor (B is a datatype and A is a module) iff C is unambiguous and A.C does not exist.
        //
        // Phase 1: Add everything else.
        let mutable phase: int = 0
        // <(name: string), (p: Path)>: we get the path p if we refer to the name.
        // If the name is ambiguous, p is replaced with an empty path.
        let mutable result: Map<Path, Map<string, Path>> = Map.empty
        
        member this.addPathLowPriority(m: Path, pname: string, p: Path) =
            let pathMapOpt = result.TryFind(m)
            let pathMap = defaultArg pathMapOpt Map.empty
            if pathMap.ContainsKey(pname) then
                // ambiguous name
                let newPathMap = pathMap.Add(pname, Path [])
                result <- result.Add(m, newPathMap)
            else
                let newPathMap = pathMap.Add(pname, p)
                result <- result.Add(m, newPathMap)

        member this.addPath(m: Path, pname: string, p: Path) =
            let pathMapOpt = result.TryFind(m)
            let pathMap = defaultArg pathMapOpt Map.empty
            let newPathMap = pathMap.Add(pname, p)
            result <- result.Add(m, newPathMap)

        override this.path(ctx: Context, p: Path) =
            if phase = 0 then
                ()
            else
                // We cannot add p.name to ctx.currentDecl. We might be calling D.E.F from A.B.C.
                this.addPath(p.parent, p.name, p)
            p
        
        override this.constructor(ctx: Context, cons: DatatypeConstructor) =
            // Note: datatype constructors are not calling this.path
            if phase = 0 then
                this.addPathLowPriority(ctx.modulePath(), cons.name, ctx.currentDecl.child(cons.name))
            else
                this.addPath(ctx.currentDecl, cons.name, ctx.currentDecl.child(cons.name))
            cons
        
        override this.decl(ctx: Context, d: Decl) : Decl list =
            if phase = 0 then
                this.declDefault(ctx, d)
            else
                match d with
                | Module (n, _, _)
                | Datatype (n, _, _, _, _)
                | Class (n, _, _, _, _, _)
                | TypeDef (n, _, _, _, _, _)
                | Field (n, _, _, _, _, _, _)
                | Method (_, n, _, _, _, _, _, _, _, _, _, _, _)
                | ClassConstructor (n, _, _, _, _, _) ->
                    this.addPath(ctx.currentDecl, n, ctx.currentDecl.child(n))
                | _ -> ()
            
                match d with
                | Import it ->
                    match it with
                    | ImportDefault(_, l)
                    | ImportEquals(_, l, _) ->
                        // Special case: we want the LHS name to map to the actual path.
                        // We do not want to call this.declDefault() which calls this.path().
                        this.addPath(ctx.currentDecl, l.name, it.getPath())
                        [ d ]
                | _ -> this.declDefault(ctx, d)

        member this.gather(prog: Program) =
            phase <- 0
            this.progDefault(prog) |> ignore
            phase <- 1
            this.progDefault(prog) |> ignore
            result

    /// Returns a map from each module to all paths it exports
    type GatherExportPaths() =
        inherit Traverser.Identity()
        
        // <(name: string), (p: Path)>: we get the path p if we refer to the name.
        // If the name is ambiguous, p is replaced with an empty path.
        let mutable result: Map<Path, Map<string, Path>> = Map.empty
        
        member this.addPaths(m: Path, p: Path list) =
            let pathMapOpt = result.TryFind(m)
            let pathMap = defaultArg pathMapOpt Map.empty
            let newPathMap = List.foldBack ((fun x (y, z) -> x y z) Map.add) (List.map (fun (x: Path) -> (x.name, x)) p) pathMap
            result <- result.Add(m, newPathMap)

        override this.decl(ctx: Context, d: Decl) : Decl list =
            match d with
            | Export e ->
                this.addPaths(ctx.currentDecl, e.provides @ e.reveals)
            | _ -> ()
            this.declDefault(ctx, d)
        
        member this.gather(prog: Program, allPaths: Map<Path, Map<string, Path>>) =
            this.progDefault(prog) |> ignore
            // By default, export all paths
            Map.iter (fun m p -> if not (result.ContainsKey(m)) then result <- result.Add(m, p)) allPaths
            result

    /// Returns a map from each module to its visible paths
    type GatherVisiblePaths() =
        inherit Traverser.Identity()
        
        // Imported names have lower priorities than native names.
        let mutable exportPaths: Map<Path, Map<string, Path>> = Map.empty
        // <(name: string), (p: Path)>: we get the path p if we refer to the name.
        // If the name is ambiguous, p is replaced with an empty path.
        let mutable result: Map<Path, Map<string, Path>> = Map.empty
        
        member this.addPathsLowPriority(m: Path, ps: Map<string, Path>) =
            // If both sets contain a name, make it (name, Path []).
            // if exactly one of the set contains a name, make it (name, p).
            let pathMapOpt = result.TryFind(m)
            let pathMap = defaultArg pathMapOpt Map.empty
            let ambiguousMap, pathMap1 = Map.partition (fun name p -> ps.ContainsKey(name)) pathMap
            let pathMap2 = Map.foldBack Map.add (Map.map (fun name p -> Path []) ambiguousMap) pathMap1
            let pathMap3 = Map.foldBack Map.add (Map.filter (fun name p -> not (pathMap2.ContainsKey(name))) ps) pathMap2
            result <- result.Add(m, pathMap3)

        member this.addPaths(m: Path, ps: Map<string, Path>) =
            let pathMapOpt = result.TryFind(m)
            let pathMap = defaultArg pathMapOpt Map.empty
            let newPathMap = Map.foldBack Map.add ps pathMap
            result <- result.Add(m, newPathMap)

        override this.decl(ctx: Context, d: Decl) : Decl list =
            match d with
            | Import it ->
                if it.isOpened() then
                    this.addPathsLowPriority(ctx.currentDecl, exportPaths[it.getPath()])
            | _ -> ()
            this.declDefault(ctx, d)
        
        member this.gather(prog: Program, allPaths: Map<Path, Map<string, Path>>) =
            exportPaths <- GatherExportPaths().gather(prog, allPaths)
            // Deal with imported paths first.
            this.progDefault(prog) |> ignore
            // Add all native paths.
            allPaths |> Map.iter (fun m ps -> this.addPaths(m, ps))
            result

    /// makes path unqualified if they are relative to the current method or an opened module
    /// (Dafny complains when we print out fully qualified names in some cases)
    type UnqualifyPaths() =
        inherit Traverser.Identity()
        
        let mutable visiblePaths: Map<Path, Map<string, Path>> = Map.empty

        override this.ToString() =
            "shortening paths by removing redundant qualification"

        /// remove opened imported path from a path
        member this.consumeImportPath (p: Path) (currentMethodPath: Path) (currentModulePath: Path) (imports: ImportType list) =
            // Return the minimal unambiguous path.
            //
            // Use LHS in ImportEquals if the path is imported with ImportEquals.
            let importEqual = List.tryFind (fun (im: ImportType) -> match im with
                                                                    | ImportDefault _ -> false
                                                                    | ImportEquals(_, _, rhsDir) -> rhsDir.isAncestorOf(p)) imports
            let pInImportEqual = Option.fold (fun (p: Path) (im: ImportType) -> match im with
                                                                                | ImportDefault _ -> p
                                                                                | ImportEquals(_, lhsDir, rhsDir) -> Path(lhsDir.name::p.names[rhsDir.names.Length..])) p importEqual
            let pInCurrentMethod = currentMethodPath.relativize pInImportEqual
            // Note that directly returning "pInCurrentMethod" here is also OK in most cases.
            //
            // If we refer to C.D.foo in module A with import opened B and import opened C,
            // and there are B.D, B.foo, C.D.foo but not B.D.foo,
            // we cannot return D.foo because D is ambiguous even if D.foo is not ambiguous.
            let currentMethodVisiblePaths = visiblePaths[currentMethodPath]
            let currentModuleVisiblePaths = visiblePaths[currentModulePath]
            let firstAmbiguousIndex = Seq.tryFindIndexBack (fun i ->
                                          let currentName = pInCurrentMethod.names[i]
                                          let currentMethodPathOpt = currentMethodVisiblePaths.TryFind(currentName)
                                          let currentPathOpt = Option.orElse (currentModuleVisiblePaths.TryFind(currentName)) currentMethodPathOpt
                                          currentPathOpt |> Option.exists (fun (currentPath: Path) -> currentPath = (Path p.names[..i + p.names.Length - pInCurrentMethod.names.Length]))
                                          ) (seq {0 .. pInCurrentMethod.names.Length - 1})
            let result = match firstAmbiguousIndex with
                         | Some len -> Path pInCurrentMethod.names[len..]
                         | None -> pInCurrentMethod
            result

        override this.path(ctx: Context, p: Path) =
            let currentMethodPath =
                if ctx.currentDecl = ctx.modulePath() then
                    ctx.currentDecl
                else
                    ctx.currentDecl.parent
            let imports = ctx.importPaths

            this.consumeImportPath p currentMethodPath (ctx.modulePath()) imports
        
        override this.decl(ctx: Context, d: Decl) : Decl list =
            match d with
            | Import importT -> 
                match importT with
                | ImportDefault (o, p) -> [ Import(ImportDefault(o, ctx.modulePath().relativize p)) ]
                | ImportEquals (o, lhs, rhs) -> [ Import(ImportEquals(o, lhs, ctx.modulePath().relativize rhs)) ]
            | _ -> this.declDefault(ctx, d)

        override this.expr(ctx: Context, expr: Expr) =
            let rcE (e: Expr) = this.expr (ctx, e)
            let rcEs (es: Expr list) = List.map rcE es
            let tryRemovingReceiver (r: Receiver) (m: Path) (result: Expr) =
                match r with
                | StaticReceiver ct ->
                    if this.path(ctx, m).names.Length = 1 then
                        result  // remove the receiver completely
                    else
                        this.exprDefault(ctx, expr)
                | ObjectReceiver _ -> this.exprDefault(ctx, expr)
            match expr with
            | EMemberRef (r, m, ts) ->
                tryRemovingReceiver r m (EVar(m.name))
            | EMethodApply (r, m, ts, es, isG) ->
                tryRemovingReceiver r m (EAnonApply(EVar(m.name), rcEs es))
            | _ -> this.exprDefault(ctx, expr)
        
        member this.run(prog: Program, gatheredVisiblePaths: Map<Path, Map<string, Path>>) =
            visiblePaths <- gatheredVisiblePaths
            this.progDefault(prog)

    /// removes duplicate includes in programs or imports in modules
    type DeduplicateImportsIncludes() =
        inherit Traverser.Identity()
        override this.ToString() = "removing duplicate imports"

        override this.prog(prog: Program) =
            let prog = this.progDefault (prog)

            let decls, _ =
                List.fold
                    (fun (decls, includes: Path list) decl ->
                        match decl with
                        | Include p ->
                            if (List.contains p includes) then
                                (decls, includes)
                            else
                                (decl :: decls, p :: includes)
                        | _ -> (decl :: decls, includes))
                    ([], [])
                    prog.decls

            { prog with decls = List.rev decls }

        override this.decl(ctx: Context, d: Decl) =
            match d with
            | Module (name, decls, meta) ->
                let newDecls, _ =
                    List.fold
                        (fun (newDecls: Decl list, paths: Path list) decl ->
                            match decl with
                            | Import it ->
                                match List.tryFind (fun x -> x.Equals(it.getPath ())) paths with
                                | Some _ -> newDecls, paths
                                | None -> decl :: newDecls, it.getPath () :: paths
                            | _ -> decl :: newDecls, paths)
                        ([], [])
                        decls

                [ Module(name, List.rev newDecls, meta) ]
            | _ -> this.declDefault (ctx, d)

    /// pulls MapBuiltinTypes.dfy, from the assembly and inserts them into a program
    type InsertTranslationFunctionsForBuiltinTypeOperators() =
        inherit Traverser.Identity()

        let retrieveResource (filename: string) : string =
            let asmb = Assembly.GetExecutingAssembly()
            // to check all assembly base names, use asmb.GetManifestResourceNames()
            let stream =
                asmb.GetManifestResourceStream($"TypeInjections.Resources.{filename}")

            let reader = new StreamReader(stream)
            reader.ReadToEnd()

        let mapBuiltinTypes = retrieveResource "MapBuiltinTypes.dfy"

        override this.ToString() =
            "inserting translation functions for built-in type operators"

        override this.prog(prog: Program) =
            { prog with
                  meta =
                      { prog.meta with
                            prelude = mapBuiltinTypes } }

    /// add an empty module if the program is effectively empty
    type AddEmptyModuleIfProgramEmpty(moduleName: string) =
        inherit Traverser.Identity()

        override this.ToString() =
            "adding empty module "
            + moduleName
            + " if necessary"

        override this.prog(prog: Program) =
            if prog.decls
               |> List.exists
                   (function
                   | Module _ -> true
                   | _ -> false) then
                prog
            else
                { prog with
                      decls = prog.decls @ [ Module(moduleName, [], emptyMeta) ] }

    /// turn lemmas into axioms
    type LemmasToAxioms() =
        inherit Traverser.Identity()
        override this.ToString() = "turning lemmas into axioms"

        override this.decl(ctx: Context, d: Decl) =
            match d with
            | Method (IsLemma, a, b, c, d, e, f, g, _, h, i, j, k) ->
                [ Method(IsLemma, a, b, c, d, e, f, g, None, h, i, j, k) ]
            | d -> this.declDefault (ctx, d)

    type Pipeline(passes: Traverser.Transform list) =
        member this.apply(prog: Program) =
            let mutable pM = prog
            
            // We need to gather the paths at the beginning before filtering joint/old/new.
            let allPaths = GatherAllPaths().gather(prog)
            let visiblePaths = GatherVisiblePaths().gather(prog, allPaths)

            passes
            |> List.iter
                (fun pass ->
                    match pass with
                    | :? UnqualifyPaths as p ->
                        Console.WriteLine(p.ToString())
                        pM <- p.run(pM, visiblePaths)
                    | _ ->
                        Console.WriteLine(pass.ToString())
                        pM <- pass.prog pM)

            pM
