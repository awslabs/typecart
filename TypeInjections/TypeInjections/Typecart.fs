namespace TypeInjections

open System
open System.IO
open System.Text.RegularExpressions
open TypeInjections.YIL

/// the high-level logic of typecart between the user-interface (see Program) and the kernel logic (see Translation)
/// Typecart takes 2 Dafny projects (OLD and NEW) and produces 1 Dafny project consisting of 4 parts:
/// - JOINT: the shared and unchanged parts of OLD and NEW
/// - OLD, NEW: variants of the inputs but without the JOINT part
/// - the key output, variously called COMBINE, PROOFS, or TRANSLATION, which
///   * translates between OLD and NEW
///   * states compatibility lemmas between OLD and NEW and generates proof stubs for them
module Typecart =

    /// interface for handling how typeCart writes out the output files
    type TypecartOutputProcessor =
        abstract member processOld : oldYIL: Program -> unit
        abstract member processNew : newYIL: Program -> unit
        abstract member processJoint : jointYIL: Program -> unit
        abstract member processProofs : translationsYIL: Program -> unit

    /// simple output instance that writes the 4 output parts into separate files
    type DefaultTypecartOutput(outFolder: string) =
        let mkdir (f: string) =
            IO.Directory.CreateDirectory(IO.Path.GetDirectoryName(f))
            |> ignore

        let write (fileName: string, p: YIL.Program) =
            let f = IO.Path.Combine(outFolder, fileName)
            mkdir f
            Console.WriteLine("writing " + f)
            let s = YIL.printer().prog (p, YIL.Context(p))
            IO.File.WriteAllText(f, s)

        interface TypecartOutputProcessor with
            member this.processOld(oldYIL: YIL.Program) = write ("old.dfy", oldYIL)
            member this.processNew(newYIL: YIL.Program) = write ("new.dfy", newYIL)
            member this.processJoint(jointYIL: YIL.Program) = write ("joint.dfy", jointYIL)
            member this.processProofs(translationsYIL: YIL.Program) = write ("proofs.dfy", translationsYIL)


    /// replace "." with "\." and "/" with "\/" to make specifying regex on filenames easier
    let private makeRegex (s: string) =
        s.Replace(".", "\.").Replace("/", "\/") |> Regex

    /// wraps around a Dafny project to allow for handling directory structure,
    type TypecartProject(project: Utils.SystemPathKind, ignorePatterns: Regex list) =
        // append .typecartignore file to ignorePatterns list
        let currDirIgnores =
            // try to find .typecartignore file in current directory
            match project with
            | Utils.D dir ->
                let objs = dir.GetFiles() |> List.ofSeq

                match List.tryFind (fun (x: FileInfo) -> x.Name.Equals(".typecartignore")) objs with
                | Some ignoreFile ->
                    ignoreFile
                        .OpenText()
                        .ReadToEnd()
                        .Split(Environment.NewLine)
                    |> List.ofSeq
                    |> List.map makeRegex
                | None -> []
            | _ -> []

        let isFilenameIgnored (fileName: string) =
            List.fold
                (fun (ignored: bool) (pattern: Regex) -> (pattern.IsMatch fileName) || ignored)
                false
                (ignorePatterns @ currDirIgnores)

        /// constructor that helps read in ignore patterns from file
        new(project: Utils.SystemPathKind, ignorePatternsFile: string option) =
            let ign =
                match ignorePatternsFile with
                | Some ignoreFile ->
                    File.ReadLines(ignoreFile)
                    |> List.ofSeq
                    |> List.map makeRegex (* every line is turned into a regular expression *)
                | None -> []

            TypecartProject(project, ign)

        // when project is just a file
        new(f: FileInfo, ignorePatterns: Regex list) = TypecartProject(Utils.F f, ignorePatterns)
        new(f: FileInfo, ignorePatternsFile: string option) = TypecartProject(Utils.F f, ignorePatternsFile)
        // when project is an entire directory structure
        new(d: DirectoryInfo, ignorePatterns: Regex list) = TypecartProject(Utils.D d, ignorePatterns)
        new(d: DirectoryInfo, ignorePatternsFile: string option) = TypecartProject(Utils.D d, ignorePatternsFile)
        // generic entrypoint when we don't know whether path is a file or directory
        new(path: string, ignorePatterns: string option) = TypecartProject(Utils.parseSystemPath path, ignorePatterns)

        // list of subdirectories of current project, empty when project is just a file
        member this.subDirectories =
            match project with
            | Utils.D currDir ->
                currDir.GetDirectories()
                |> List.ofSeq
                |> List.map (fun d -> TypecartProject(d, ignorePatterns))
            | Utils.F _ -> []

        // list of files of current project, singleton list when project is just a file
        member this.files =
            match project with
            | Utils.D currDir ->
                currDir.GetFiles()
                |> List.ofSeq
                // filter out non-dafny files
                |> List.filter
                    (fun fd ->
                        match fd.Name with
                        | Utils.Suffix ".dfy" _ -> true
                        | _ -> false)
                // filter out filenames to be ignored
                // we filter based on the fully qualified path of the filename, just like the
                // behavior of .gitignore.
                |> List.filter (fun fd -> not (isFilenameIgnored fd.FullName))
            | Utils.F file -> [ file ]

        // flattens all the files
        member this.collect() =
            this.files
            @ List.collect (fun (subProject: TypecartProject) -> subProject.collect ()) this.subDirectories

        // ****** below are the two key methods for operating on the Dafny project *****
        
        /// run Dafny: parse+type-check
        member this.toDafnyAST(projectName: string, reporter) =
            Utils.parseASTs (this.collect ()) projectName reporter

        /// run Dafny + convert to YIL
        member this.toYILProgram(projectName: string, reporter) =
            DafnyToYIL.program (this.toDafnyAST (projectName, reporter), reporter.Options)

    // ***************************************
    
    /// the high-level logic: calls the kernel on 2 Dafny projects and performs simplifications/cleanup
    type Typecart(oldYIL: Program, newYIL: Program, logger: (string -> unit) option) =
        let oldOrNewPrefix (old: bool) = if old then "Old" else "New"
        let jointPrefix = "Joint"
        let proofsPrefix = "Proofs"
        
        // all 4 parts are produced by chaining transformations, we set up the piplelines here
         
        // pipelines for transforming old, new, joint, translations
        
        // run before diffing to normalize programs and thus simplify the diffs
        let preprocessPipeline : Traverser.Transform list =
            [ Analysis.UnifyAnonymousVariableNames()
              Analysis.NormalizeEQuant() ]
        
        // joint: the paths that are moved into joint and must be removed from the project
        // old: true for OLD, false for NEW
        let oldOrNewPipeline (joint: YIL.Path list, old: bool) : Traverser.Transform list =
            [ Analysis.FilterDeclsAndPrefixImports(
                (fun p -> not (List.exists (fun (q: YIL.Path) -> q.isAncestorOf p) joint)),
                "Joint"
              )
              Analysis.LemmasToAxioms()
              Analysis.LeaveQualifiedYILForProofs()
              Analysis.UnqualifyPaths()
              Analysis.WrapTopDecls(oldOrNewPrefix (old))
              Analysis.AddImports([ "joint.dfy" ], [ "Joint" ])
              Analysis.DeduplicateImportsIncludes()
              Analysis.AddEmptyModuleIfProgramEmpty(oldOrNewPrefix (old)) ]

        let jointPipeline (joint: YIL.Path list) : Traverser.Transform list =
            [ Analysis.FilterDeclsAndPrefixImports(
                (fun p -> (List.exists (fun (q: YIL.Path) -> q.isAncestorOf (p)) joint)),
                "(no prefix)"
              )
              Analysis.LemmasToAxioms()
              Analysis.LeaveQualifiedYILForProofs()
              Analysis.UnqualifyPaths()
              Analysis.WrapTopDecls(jointPrefix)
              Analysis.DeduplicateImportsIncludes()
              Analysis.AddEmptyModuleIfProgramEmpty(jointPrefix) ]

        let proofsPipeline : Traverser.Transform list =
            [ Analysis.InlineIdentityTranslationFunctions()
              Analysis.RemoveRedundantEBLock()
              Analysis.UnqualifyPaths()
              Analysis.WrapTopDecls(proofsPrefix)
              Analysis.AddImports(
                  [ "joint.dfy"; "old.dfy"; "new.dfy" ],
                  [ "Joint"
                    "Old"
                    "New"
                    "Translations" ]
              )
              Analysis.DeduplicateImportsIncludes()
              Analysis.InsertTranslationFunctionsForBuiltinTypeOperators() ]

        // constructor without a logger instance
        new(oldYIL: Program, newYIL: Program) = Typecart(oldYIL, newYIL, None)
        // constructor with a logger instance
        new(oldYIL: Program, newYIL: Program, logger: string -> unit) = Typecart(oldYIL, newYIL, Some logger)

        member this.logger s =
            match logger with
            | None -> ()
            | Some logger -> logger s

        /// ***** the entry point for running the typecart loigc
        member this.go(outputWriter: TypecartOutputProcessor) =
            // only used for debugging: tests the transformation code
            // Traverser.test oldYIL
            
            this.logger "***** preprocessing the two programs"
            let oldYIL, _ = Analysis.Pipeline(preprocessPipeline).apply (oldYIL, [])
            let newYIL, _ = Analysis.Pipeline(preprocessPipeline).apply (newYIL, [])

            // diff the programs
            this.logger "***** diffing the two programs"
            let diff = Differ.prog (oldYIL, newYIL)
            let diffS = (Diff.Printer()).prog diff
            this.logger diffS

            // generate translation
            this.logger "***** generating translation code"
            let proofsYIL, jointPaths = Translation.prog (oldYIL, newYIL, "Proofs", diff)

            // emitting output
            this.logger "************ emitting output"
            this.logger "***** joint"
            let jointYILresult, jointYILpreserved =
                Analysis.Pipeline(jointPipeline jointPaths).apply (newYIL, [])
            outputWriter.processJoint (jointYILresult)

            this.logger "***** old"
            let oldYILresult, oldYILpreserved =
                Analysis.Pipeline(oldOrNewPipeline (jointPaths, true)).apply (oldYIL, [])
            outputWriter.processOld (oldYILresult)

            this.logger "***** new"
            let newYILresult, newYILpreserved =
                Analysis.Pipeline(oldOrNewPipeline (jointPaths, false)).apply (newYIL, [])
            outputWriter.processNew (newYILresult)

            this.logger "***** proofs"
            let proofsYILresult, _ =
                Analysis.Pipeline(proofsPipeline).apply (
                        proofsYIL,
                        [ Analysis.WrapTopDecls(jointPrefix).prog jointYILpreserved
                          Analysis.WrapTopDecls(oldOrNewPrefix true).prog oldYILpreserved
                          Analysis.WrapTopDecls(oldOrNewPrefix false).prog newYILpreserved ]
                    )
            outputWriter.processProofs (proofsYILresult)
