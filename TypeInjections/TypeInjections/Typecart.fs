namespace TypeInjections

open System
open System.IO
open System.Text.RegularExpressions
open TypeInjections.YIL

// TypecartAPI exposes typeCart functionalities as a reusable component
module Typecart =

    // interface for handling how typeCart writes out the diffed files
    type TypecartOutputProcessor =
        abstract member processOld : oldYIL: Program -> unit
        abstract member processNew : newYIL: Program -> unit
        abstract member processJoint : jointYIL: Program -> unit
        abstract member processCombine : translationsYIL: Program -> unit

    // Sample output-writing interface for diffing two files
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
            member this.processCombine(translationsYIL: YIL.Program) = write ("combine.dfy", translationsYIL)


    // replace "." with "\." and "/" with "\/" to make specifying regex on filenames easier
    let private makeRegex (s: string) =
        s.Replace(".", "\.").Replace("/", "\/") |> Regex

    // the class TypecartProject defines the input directory scope,
    // typeCart reads in every file in the directory structure of a project, and produce a diff
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

        // constructor that helps read in ignore patterns from file
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

        // turn the directory into a single Dafny AST
        member this.toDafnyAST(projectName: string, reporter) =
            Utils.parseASTs (this.collect ()) projectName reporter

        // turn dafny AST representation of directory into a YIL AST
        member this.toYILProgram(projectName: string, reporter) =
            this.toDafnyAST (projectName, reporter)
            |> DafnyToYIL.program

    // API entry
    type Typecart(oldYIL: Program, newYIL: Program, logger: (string -> unit) option) =
        let oldOrNewPrefix (old: bool) = if old then "Old" else "New"
        let jointPrefix = "Joint"
        let combinePrefix = "Combine"
        // pipelines for transforming old, new, joint, translations
        let oldOrNewPipeline (joint: YIL.Path list, old: bool) : Traverser.Transform list =
            [ Analysis.FilterDecls(fun p -> not (List.contains p joint))
              Analysis.LemmasToAxioms()
              Analysis.UnqualifyPaths()
              Analysis.PrefixTopDecls(oldOrNewPrefix (old))
              Analysis.PrefixUnfoundImports("Joint")
              Analysis.AddImports([ "joint.dfy" ], [ "Joint" ])
              Analysis.DeduplicateImportsIncludes()
              Analysis.AddEmptyModuleIfProgramEmpty(oldOrNewPrefix (old)) ]

        let jointPipeline (joint: YIL.Path list) : Traverser.Transform list =
            [ Analysis.FilterDecls(fun p -> List.contains p joint)
              Analysis.LemmasToAxioms()
              Analysis.UnqualifyPaths()
              Analysis.PrefixTopDecls(jointPrefix)
              Analysis.DeduplicateImportsIncludes()
              Analysis.AddEmptyModuleIfProgramEmpty(jointPrefix) ]

        let combinePipeline : Traverser.Transform list =
            [ Analysis.AddImports([ "joint.dfy"; "old.dfy"; "new.dfy" ], [ "Joint"; "Old"; "New"; "Translations" ])
              Analysis.UnqualifyPaths()
              Analysis.PrefixTopDecls(combinePrefix)
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

        /// run typecart on oldYIL and newYIL and perform program-level diffing with module granularity
        member this.go(outputWriter: TypecartOutputProcessor) =
            // for debugging: tests the transformation code
            // Traverser.test oldYIL
            // diff the programs
            this.logger "***** diffing the two programs"
            let diff = Differ.prog (oldYIL, newYIL)
            let diffS = (Diff.Printer()).prog diff
            this.logger diffS

            // generate translation
            this.logger "***** generating translation code"

            let combineYIL, jointPaths =
                Translation.prog (oldYIL, "Combine", diff)

            // emitting output
            this.logger "************ emitting output"
            this.logger "***** joint"

            Analysis
                .Pipeline(jointPipeline jointPaths)
                .apply newYIL
            |> outputWriter.processJoint

            this.logger "***** old"

            Analysis
                .Pipeline(oldOrNewPipeline (jointPaths, true))
                .apply oldYIL
            |> outputWriter.processOld

            this.logger "***** new"

            Analysis
                .Pipeline(oldOrNewPipeline (jointPaths, false))
                .apply newYIL
            |> outputWriter.processNew

            this.logger "***** combine"

            Analysis
                .Pipeline(combinePipeline)
                .apply combineYIL
            |> outputWriter.processCombine

    let typecart (oldYIL: Program, newYIL: Program, logger: string -> unit) = Typecart(oldYIL, newYIL, logger)
