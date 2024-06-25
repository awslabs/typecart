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

    /// Returns a set of all non-module decls (in Set<Path>) that uses anything in "start".
    /// If "start" contains a module, however, it will also return that module.
    type GatherDeclsUsingPaths(start: Set<Path>) =
        inherit Traverser.Identity()
        
        let mutable result: Set<Path> = Set.empty
        
        override this.path(ctx: Context, p: Path): Path =
            // Do not include modules because they do not "use" anything
            if start.Contains(p) && (not (ctx.lookupCurrent().isModule())) then
                result <- result.Add(ctx.currentDecl)
            p

        override this.constructor(ctx: Context, cons: DatatypeConstructor) =
            // Note: datatype constructors are not calling this.path
            if start.Contains(ctx.currentDecl.child(cons.name)) then
                result <- result.Add(ctx.currentDecl)
            
            let insT = this.localDeclList (ctx, cons.ins)

            { name = cons.name
              ins = insT
              meta = cons.meta }
        
        override this.decl(ctx: Context, d: Decl) : Decl list =
            // Include the decls themselves.
            match d with
            | Module (n, _, _)
            | Datatype (n, _, _, _, _)
            | Class (n, _, _, _, _, _)
            | TypeDef (n, _, _, _, _, _)
            | Field (n, _, _, _, _, _, _)
            | Method (_, n, _, _, _, _, _, _, _, _, _, _, _)
            | ClassConstructor (n, _, _, _, _, _) ->
                if start.Contains(ctx.currentDecl.child(n)) then
                    result <- result.Add(ctx.currentDecl.child(n))
            | _ -> ()
            this.declDefault(ctx, d)
            
        member this.gather(prog: Program) =
            this.progDefault(prog) |> ignore
            result
        
    let dependencyClosureByGatherDeclsUsingPaths (prog: Program, start: Set<Path>) =
        let mutable prev_closure: Set<Path> = Set.empty
        let mutable closure = start

        while prev_closure <> closure do
            prev_closure <- closure
            closure <- GatherDeclsUsingPaths(closure).gather(prog)

        closure

    /// Returns a set of paths that is all children (subtrees) of a input set of paths. (unused)
    type GatherPathsSubtree(start: Set<Path>) =
        inherit Traverser.Identity()
        
        let mutable result: Set<Path> = start
        
        member this.addPath(p: Path) =
            if Set.exists (fun (q: Path) -> q.isAncestorOf(p)) start then
                result <- result.Add(p)

        override this.path(ctx: Context, p: Path) =
            this.addPath(p)
            p
        
        override this.constructor(ctx: Context, cons: DatatypeConstructor) =
            // Note: datatype constructors are not calling this.path
            this.addPath(ctx.currentDecl.child(cons.name))
            let insT = this.localDeclList (ctx, cons.ins)

            { name = cons.name
              ins = insT
              meta = cons.meta }
        
        override this.decl(ctx: Context, d: Decl) : Decl list =
            match d with
            | Module (n, _, _)
            | Datatype (n, _, _, _, _)
            | Class (n, _, _, _, _, _)
            | TypeDef (n, _, _, _, _, _)
            | Field (n, _, _, _, _, _, _)
            | Method (_, n, _, _, _, _, _, _, _, _, _, _, _)
            | ClassConstructor (n, _, _, _, _, _) ->
                this.addPath(ctx.currentDecl.child(n))
            | _ -> ()
            
            this.declDefault(ctx, d)

        member this.gather(prog: Program) =
            this.progDefault(prog) |> ignore
            result

    /// filters declarations by applying a predicate to their path;
    /// prefix imports to removed declarations
    type FilterDeclsAndPrefixImports(keep: Path -> bool, prefix: string) =
        inherit Traverser.Identity()
        override this.ToString() = "filtering declarations and prefixing imports with " + prefix

        override this.decl(ctx: Context, decl: Decl) =
            match decl with
            | Module(name, _, _) -> if keep (ctx.currentDecl.child (name)) then
                                        this.declDefault(ctx, decl)
                                    else
                                        []
            | Import im -> if keep (im.getPath()) then
                               [ decl ]
                           else
                               [ Import(im.prefix prefix) ]
            | _ -> this.declDefault(ctx, decl)

        override this.prog(p: Program) =
            let dsF =
                p.decls
                |> List.filter (fun (d: Decl) -> keep (Path [ d.name ]))

            let pF = { p with decls = dsF }
            this.progDefault(pF)

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

    /// wraps all toplevel modules into a module (only to be called on programs)
    type WrapTopDecls(pref: string) =
        inherit Traverser.Identity()
        override this.ToString() = "wrapping toplevel decls with module " + pref

        override this.prog(prog: Program) =
            { name = prog.name
              decls = [ Module(pref, prog.decls, emptyMeta) ]
              meta = prog.meta }
    
    /// Returns a map from each path to all children in it (but not in nested modules or in datatypes)
    type GatherAllPaths() =
        inherit Traverser.Identity()
        
        // Datatype constructors have lower priorities than local names.
        //
        // Phase 0: Add datatype constructor names to the modules with priority 1.
        // We can use C directly in A if A.B.C is a datatype
        // constructor (B is a datatype and A is a module) iff C is unambiguous and A.C does not exist.
        //
        // Phase 1: Add everything else with priority 2.
        let mutable phase: int = 0
        // <(name: string), (p: Path) * (priority: int)>: we get the path p if we refer to the name.
        // If the name is ambiguous, p is replaced with an empty path.
        let mutable result: Map<Path, Map<string, Path * int>> = Map.empty
        
        member this.addPathLowPriority(m: Path, pname: string, p: Path) =
            let pathMapOpt = result.TryFind(m)
            let pathMap = defaultArg pathMapOpt Map.empty
            if pathMap.ContainsKey(pname) then
                // ambiguous name
                let newPathMap = pathMap.Add(pname, (Path [], 1))
                result <- result.Add(m, newPathMap)
            else
                let newPathMap = pathMap.Add(pname, (p, 1))
                result <- result.Add(m, newPathMap)

        member this.addPath(m: Path, pname: string, p: Path) =
            let pathMapOpt = result.TryFind(m)
            let pathMap = defaultArg pathMapOpt Map.empty
            let newPathMap = pathMap.Add(pname, (p, 2))
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
            let insT = this.localDeclList (ctx, cons.ins)

            { name = cons.name
              ins = insT
              meta = cons.meta }
        
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
                    | ImportDefault (_, l) ->
                        this.addPath(ctx.currentDecl, l.name, l)
                        [ d ]
                    | ImportEquals(_, l, r) ->
                        // Special case: we want the LHS name to map to the actual path.
                        // We do not want to call this.declDefault() which calls this.path().
                        this.addPath(ctx.currentDecl, l, r)
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
        
        // <(name: string), (p: Path) * (priority: int)>: we get the path p if we refer to the name.
        // If the name is ambiguous, p is replaced with an empty path.
        // All exported paths have priority 1.
        let mutable result: Map<Path, Map<string, Path * int>> = Map.empty
        
        member this.addPaths(m: Path, p: Path list) =
            let pathMapOpt = result.TryFind(m)
            let pathMap = defaultArg pathMapOpt Map.empty
            let newPathMap = List.foldBack ((fun x (y, z) -> x y z) Map.add) (List.map (fun (x: Path) -> (x.name, (x, 1))) p) pathMap
            result <- result.Add(m, newPathMap)

        override this.decl(ctx: Context, d: Decl) : Decl list =
            match d with
            | Export e ->
                this.addPaths(ctx.currentDecl, e.provides @ e.reveals)
            | _ -> ()
            this.declDefault(ctx, d)
        
        member this.gather(prog: Program, allPaths: Map<Path, Map<string, Path * int>>) =
            this.progDefault(prog) |> ignore
            // By default, export all paths
            Map.iter (fun m p -> if not (result.ContainsKey(m)) then result <- result.Add(m, (Map.map (fun n pr -> (fst pr, 1)) p))) allPaths
            result

    /// Returns a map from each module to its visible paths
    type GatherVisiblePaths() =
        inherit Traverser.Identity()
        
        // Imported names have lower priorities than native names...
        // Except for datatype constructors where they have the same priorities.
        let mutable exportPaths: Map<Path, Map<string, Path * int>> = Map.empty
        // <(name: string), (p: Path)>: we get the path p if we refer to the name.
        // If the name is ambiguous, p is replaced with an empty path.
        let mutable result: Map<Path, Map<string, Path * int>> = Map.empty
        
        member this.addPathsLowPriority(m: Path, ps: Map<string, Path * int>) =
            // If both sets contain a name, make it (name, Path []).
            // if exactly one of the set contains a name, make it (name, p).
            // Priority is not used here (assume to be 1).
            let pathMapOpt = result.TryFind(m)
            let pathMap = defaultArg pathMapOpt Map.empty
            let ambiguousMap, pathMap1 = Map.partition (fun name p -> ps.ContainsKey(name)) pathMap
            let pathMap2 = Map.foldBack Map.add (Map.map (fun name p -> (Path [], snd p)) ambiguousMap) pathMap1
            let pathMap3 = Map.foldBack Map.add (Map.filter (fun name p -> not (pathMap2.ContainsKey(name))) ps) pathMap2
            result <- result.Add(m, pathMap3)

        member this.addPaths(m: Path, ps: Map<string, Path * int>) =
            let ps1, ps2 = Map.partition (fun name p -> (snd p) = 1) ps
            this.addPathsLowPriority(m, ps1)
            let pathMapOpt = result.TryFind(m)
            let pathMap = defaultArg pathMapOpt Map.empty
            let newPathMap = Map.foldBack Map.add ps2 pathMap
            result <- result.Add(m, newPathMap)

        override this.decl(ctx: Context, d: Decl) : Decl list =
            match d with
            | Import it ->
                if it.isOpened() then
                    this.addPathsLowPriority(ctx.currentDecl, exportPaths[it.getPath()])
            | _ -> ()
            this.declDefault(ctx, d)
        
        member this.gather(prog: Program, allPaths: Map<Path, Map<string, Path * int>>) =
            exportPaths <- GatherExportPaths().gather(prog, allPaths)
            // Deal with imported paths first.
            this.progDefault(prog) |> ignore
            // Add all native paths.
            allPaths |> Map.iter (fun m ps -> this.addPaths(m, ps))
            // Remove the priority information.
            result |> Map.map (fun m ps -> Map.map (fun n p -> fst p) ps)

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
                                                                                | ImportEquals(_, lhsDir, rhsDir) -> Path(lhsDir::p.names[rhsDir.names.Length..])) p importEqual
            let pInCurrentMethod = currentMethodPath.relativize pInImportEqual
            // Note that directly returning "pInCurrentMethod" here is also OK in most cases.
            //
            // If we refer to C.D.foo in module A with import opened B and import opened C,
            // and there are B.D, B.foo, C.D.foo but not B.D.foo,
            // we cannot return D.foo because D is ambiguous even if D.foo is not ambiguous.
            let currentMethodVisiblePaths = visiblePaths[currentMethodPath]
            let currentModuleVisiblePaths = visiblePaths[currentModulePath]
            let firstUnAmbiguousIndex = Seq.tryFindIndexBack (fun i ->
                                          let currentName = pInCurrentMethod.names[i]
                                          let currentMethodPathOpt = currentMethodVisiblePaths.TryFind(currentName)
                                          let currentPathOpt = Option.orElse (currentModuleVisiblePaths.TryFind(currentName)) currentMethodPathOpt
                                          currentPathOpt |> Option.exists (fun (currentPath: Path) -> currentPath = (Path p.names[..i + p.names.Length - pInCurrentMethod.names.Length]))
                                          ) (seq {0 .. pInCurrentMethod.names.Length - 1})
            let result = match firstUnAmbiguousIndex with
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
                | StaticReceiver _ ->
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
                [ Method(IsLemma, a, b, c, d, e, f, g, None, h, i, j, k.addAttribute("axiom", [])) ]
            | d -> this.declDefault (ctx, d)
    
    /// Returns the set of identity translation functions
    type GatherIdentityTranslationFunctions() =
        inherit Traverser.Identity()
        
        let mutable result: Set<Path> = Set.empty

        override this.decl(ctx: Context, d: Decl) : Decl list =
            match d with
            | Method(methodType, name, tpvars, inputSpec, outputSpec, modifies, reads, decreases, body, ghost, isStatic, isOpaque, meta) ->
                if (name.EndsWith("_forward") || name.EndsWith("_backward")) && inputSpec.decls.Length = 1 &&
                   outputSpec.decls.Length = 1 && inputSpec.decls[0].tp = outputSpec.decls[0].tp then
                      result <- result.Add(ctx.currentDecl.child(name))
            | _ -> ()
            this.declDefault(ctx, d)
        
        member this.gather(prog: Program) =
            this.progDefault(prog) |> ignore
            result

    /// inline identity translation functions
    type InlineIdentityTranslationFunctions() =
        inherit Traverser.Identity()
        
        let mutable identities: Set<Path> = Set.empty
        
        override this.ToString() = "inlining identity translation functions"
        
        override this.expr(ctx: Context, expr: Expr) =
            match expr with
            | EMethodApply (r, m, ts, es, isG) when es.Length = 1 && identities.Contains(m) ->
                this.exprDefault(ctx, es[0])  // extract the argument and dive inside
            | _ -> this.exprDefault(ctx, expr)
        
        override this.decl(ctx: Context, d: Decl) =
            match d with
            | Method (_, name, _, _, _, _, _, _, _, _, _, _, _) when identities.Contains(ctx.currentDecl.child(name)) ->
                []  // remove the function
            | _ -> this.declDefault (ctx, d)
        
        override this.prog(p: Program) =
            identities <- GatherIdentityTranslationFunctions().gather(p)
            this.progDefault(p)
    
    /// turn anonymous variable names "_v1" into "_".
    /// This is the expedient way to let Differ treat expressions with the same structure but different
    /// anonymous variable names as the same. This is correct as long as we use Differ.exprO and Differ.expr
    /// only in the context without any anonymous variables (which is true).
    /// A more systematic approach would be to implement alpha-equality in the Differ, and also restore the
    /// original anonymous variable name in DafnyToYIL.
    type UnifyAnonymousVariableNames() =
        inherit Traverser.Identity()
        override this.ToString() = "unifying anonymous variable names"
        
        override this.localDecl(ctx: Context, ld: LocalDecl) =
            LocalDecl((if ld.name.StartsWith("_") then "_" else ld.name), this.tp (ctx, ld.tp), ld.ghost)
        
        override this.expr(ctx: Context, expr: Expr) =
            match expr with
            | EVar name ->
                if name.StartsWith("_") then
                    EVar "_"
                else
                    expr
            | _ -> this.exprDefault(ctx, expr)
    
    /// Move the condition of forall expressions out of the body of the expression.
    type NormalizeEQuant() =
        inherit Traverser.Identity()
        override this.ToString() = "normalizing forall expressions"
        
        override this.localDecl(ctx: Context, ld: LocalDecl) =
            LocalDecl((if ld.name.StartsWith("_") then "_" else ld.name), this.tp (ctx, ld.tp), ld.ghost)
        
        override this.expr(ctx: Context, expr: Expr) =
            match expr with
            | EQuant (quant, ld, cond, ens, body) when quant = Quantifier.Forall ->
                match cond with
                | Some _ -> this.exprDefault(ctx, expr)
                | None ->
                    match body with
                    | EBinOpApply (op, arg1, arg2) when Printer(true).binaryOperatorResolve (op) = "==>" ->
                        let ctxE = ctx.add ld
                        let ensT = this.conditionList (ctxE, ens)
                        let arg1T = this.expr (ctxE, arg1)
                        let arg2T = this.expr (ctxE, arg2)
                        EQuant (quant, this.localDeclList (ctx, ld), Some arg1T, ensT, arg2T)
                    | _ ->
                        this.exprDefault(ctx, expr)
            | _ -> this.exprDefault(ctx, expr)
        
    /// EBlock [ ..., EBlock [ exprs ], ... ] => EBlock [ ..., exprs, ... ]
    type RemoveRedundantEBLock() =
        inherit Traverser.Identity()
        override this.ToString() = "removing redundant blocks"
        override this.expr(ctx: Context, expr: Expr) =
            match expr with
            | EBlock es ->
                let unblock exprs = List.concat (List.map (fun e ->
                    match e with
                    | EBlock esInside -> esInside
                    | _ -> [ e ]) exprs)
                EBlock (this.exprList(ctx, unblock (unblock es))) // assume no more than 2 consecutive redundant layers
            | _ -> this.exprDefault(ctx, expr)
    
    /// we need to leave a qualified version of YIL for proofs to resolve names
    type LeaveQualifiedYILForProofs() =
        inherit Traverser.Identity()
        override this.ToString() = "leaving qualified YIL for Proofs"

    type Pipeline(passes: Traverser.Transform list) =
        member this.apply(prog: Program, otherProgs: Program list) =
            let mutable pM = prog
            let mutable pPreserved = prog
            
            // We need to gather the paths at the beginning before filtering joint/old/new.
            let allPathsInProg = GatherAllPaths().gather(prog)
            let addPaths (m: Path) (ps: Map<string, Path * int>) (result: Map<Path, Map<string, Path * int>>): Map<Path, Map<string, Path * int>> =
                let pathMapOpt = result.TryFind(m)
                let pathMap = defaultArg pathMapOpt Map.empty
                let addPath (s: string) (p: Path * int) (pm: Map<string, Path * int>) =
                    if pm.ContainsKey(s) then
                        if (snd (pm[s])) > 1 then
                            // We should not be updating paths here because the new one has a lower priority.
                            pm
                        else
                            pm.Add(s, (Path [], 1))
                    else
                        pm.Add(s, (fst p, 1))  // imported paths have priority 1
                let newPathMap = Map.foldBack addPath ps pathMap
                result.Add(m, newPathMap)
            let allPaths = List.foldBack (Map.foldBack addPaths) (List.map (GatherAllPaths().gather) otherProgs) allPathsInProg
            let visiblePaths = GatherVisiblePaths().gather(prog, allPaths)

            passes
            |> List.iter
                (fun pass ->
                    match pass with
                    | :? UnqualifyPaths as p ->
                        Console.WriteLine(p.ToString())
                        pM <- p.run(pM, visiblePaths)
                    | :? LeaveQualifiedYILForProofs as p ->
                        Console.WriteLine(p.ToString())
                        pPreserved <- pM
                    | _ ->
                        Console.WriteLine(pass.ToString())
                        pM <- pass.prog pM)

            pM, pPreserved
