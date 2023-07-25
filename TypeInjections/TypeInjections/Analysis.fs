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
                                    if existingPrefix <> "" then
                                        decl  // do not prefix it
                                    else
                                        Import(it.prefix prefix)
                            | _ -> decl)
                        decls

                [ Module(name, filtDecls, meta) ]
            | _ -> this.declDefault (ctx, decl)

        override this.prog(prog: Program) =
            let decls = prog.decls in

            let ctx =
                List.fold
                    (fun (ctx: Context) decl ->
                        match decl with
                        | Module (name, _, _) -> ctx.addImport (ImportDefault(false, Path [ name ]))
                        | _ -> ctx)
                    (Context(prog))
                    decls

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
    
    type GatherAllPaths() =
        inherit Traverser.Identity()
        
        let mutable result: Set<Path> = Set.empty
        
        override this.path(ctx: Context, p: Path) =
            result <- result.Add(p)
            p
        
        override this.decl(ctx: Context, d: Decl) : Decl list =
            match d with
            | Module (n, _, _)
            | Datatype (n, _, _, _, _)
            | Class (n, _, _, _, _, _)
            | TypeDef (n, _, _, _, _, _)
            | Field (n, _, _, _, _, _, _)
            | Method (_, n, _, _, _, _, _, _, _, _, _, _, _)
            | ClassConstructor (n, _, _, _, _, _) ->
                result <- result.Add(ctx.currentDecl.child(n))
            | _ -> ()
            this.declDefault(ctx, d)
        
        member this.gather (prog: Program) =
            this.progDefault(prog) |> ignore
            result

    /// makes path unqualified if they are relative to the current method or an opened module
    /// (Dafny complains when we print out fully qualified names in some cases)
    type UnqualifyPaths() =
        inherit Traverser.Identity()
        
        let mutable allPaths: Set<Path> = Set.empty

        override this.ToString() =
            "shortening paths by removing redundant qualification"
        /// remove opened imported path from a path
        member this.consumeImportPath (p: Path) (pInCurrentMethod: Path) (currentModulePaths: Path list) (imports: ImportType list) =
            // Return the minimal unambiguous path.
            // Note that directly returning "pInCurrentMethod" here is also OK, just resulting in longer Dafny code.
            let openedImports = List.map (fun (import: ImportType) -> (if import.isOpened() then import.getPath() else Path [])) imports |> List.filter (fun (q: Path) -> q.names.Length > 0)
            let visibleModules = currentModulePaths @ openedImports
            let visiblePaths = Set.filter (fun (q: Path) -> q.name = p.name && List.exists (fun (importPath: Path) -> importPath.isAncestorOf(q)) visibleModules) allPaths
            let consumedPaths = List.map (fun (q: Path) -> q.relativize p) visibleModules
            let minimalPath = List.fold (fun (p1: Path) (p2: Path) -> if p1.names.Length <= p2.names.Length then p1 else p2) pInCurrentMethod consumedPaths
            let minimalUnambiguousPathLength = Seq.tryFindIndexBack (fun i -> 
                let currentPath = Path pInCurrentMethod.names[i..]
                let visiblePathsWithSameSuffix = Set.filter (fun (q: Path) -> currentPath.isSuffixOf(q)) visiblePaths
                visiblePathsWithSameSuffix.Count = 1) (seq {0 .. pInCurrentMethod.names.Length - minimalPath.names.Length})
            match minimalUnambiguousPathLength with
            | Some len -> Path pInCurrentMethod.names[len..]
            | None -> pInCurrentMethod

        override this.path(ctx: Context, p: Path) =
            let currentMethodPath =
                if ctx.currentDecl = ctx.modulePath() then
                    ctx.currentDecl
                else
                    ctx.currentDecl.parent

            let p2 = currentMethodPath.relativize p
            let imports = ctx.importPaths
            this.consumeImportPath p p2 [ currentMethodPath; ctx.modulePath() ] imports
        
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
        
        override this.prog(prog: Program) =
            allPaths <- GatherAllPaths().gather(prog)
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

            passes
            |> List.iter
                (fun pass ->
                    Console.WriteLine(pass.ToString())
                    pM <- pass.prog pM)

            pM
