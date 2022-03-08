// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT

namespace TypeInjections

open Microsoft.Dafny

module Program =

    let log (s: string) = System.Console.WriteLine(s)
    let logObject (s: string) (arg: obj) = System.Console.WriteLine(s, arg)

    // extraFile contains the extra mapping function that we might need to paste in the output file
    let extraDafnyFile (root: string) (extraFilename: string Option) : DafnyFile option =
        let rt =
            System
                .IO
                .Directory
                .GetParent(
                    System.IO.Directory.GetParent(root).FullName
                )
                .FullName

        let rt =
            System.IO.Path.Combine([| rt; "LibFunctions" |])

        Option.bind (fun file -> Some(DafnyFile(System.IO.Path.Combine([| rt; file |])))) extraFilename

    let initDafny : ConsoleErrorReporter =
        // preparations, adapted from DafnyDriver.Main
        let reporter = ConsoleErrorReporter()
        let options = DafnyOptions(reporter)
        log "***** searching for DafnyPrelude.bpl"
        (* Dafny initialization always call Boogie initialization, which depends on loading DafnyPrelude.bpl, a Boogie file
               implementing the Dafny built-ins. Even though we will not run Boogie, we need to go through this step.
               But Dafny cannot find the file in dafny/Binaries because it uses the location of the current program to locate it.
               So we copy the file into the current project and point Dafny to it.
            *)
        // get the directory of the running program
        let codebase = Utils.location
        //ToDo: the orElse branch could only be checked if the first test failed
        let dafnyPrelude =
            // When using the binary installation of Dafny:
            Utils.findFile (codebase, "dafny", "DafnyPrelude.bpl")
            // When using Dafny built from source:
            |> Option.orElse (Utils.findFile (codebase, "dafny/Binaries", "DafnyPrelude.bpl"))
            |> Option.get

        System.Console.WriteLine(dafnyPrelude)

        let dafnyPreludeDir =
            Utils.findDirectory (codebase, "dafny", "DafnyPrelude.bpl")
            |> Option.get

        logObject "found in: {0}" dafnyPreludeDir

        log "***** initialising Dafny"
        options.DafnyPrelude <- dafnyPrelude
        DafnyOptions.Install(options)
        log "***** Dafny initialised"

        reporter

    let parseAST
        (dafnyFile: DafnyFile)
        (programName: string)
        (reporter: ConsoleErrorReporter)
        (dafnyProgram: outref<Program>)
        : unit =
        logObject "***** calling Dafny parser and checker for {0}" dafnyFile.SourceFileName
        let dafnyFiles = [ dafnyFile ]

        let err =
            Main.ParseCheck(Utils.toIList dafnyFiles, programName, reporter, &dafnyProgram)

        if err <> null && err <> "" then
            failwith ("Dafny errors: " + err)

    // Print the generated type functions to the given outputPath. All given parts are relative to the root
    let runTypeCart file1 file2 root (extraFilename: string Option) (includeLemmas: bool) outputFile : unit =

        let reporter = initDafny

        // the main call to dafny, adapted from DafnyDriver.ProcessFiles
        let dafnyFile1 = DafnyFile(file1)
        let programName1 = "old"
        let mutable dafnyProgram1 = Unchecked.defaultof<Program>
        parseAST dafnyFile1 programName1 reporter &dafnyProgram1

        let dafnyFile2 = DafnyFile(file2)
        let programName2 = "new"
        let mutable dafnyProgram2 = Unchecked.defaultof<Program>
        parseAST dafnyFile2 programName2 reporter &dafnyProgram2

        // inspect the results
        log "***** Running typeCart"
        InjectionIO.findEqTypes (&dafnyProgram1, &dafnyProgram2)

        // extraFile contains the extra mapping function that we might need to paste in the output file
        let extraFile = extraDafnyFile root extraFilename

        // At some points, we want to add extra functions manually. We could write them directly in the AST, but this is
        // very tedious, so we parse them from a file.
        match extraFile with
        | None -> ()
        | Some file ->
            let programName = "extra"
            let mutable dafnyProgram = Unchecked.defaultof<Program>
            parseAST file programName reporter &dafnyProgram
            // inspect the results
            log "***** traversing Dafny AST for extra file"
            InjectionIO.parseExtraFunctions dafnyProgram

        let fileName1 = System.IO.Path.GetFileName(file1)
        let fileName2 = System.IO.Path.GetFileName(file2)

        let outputPath =
            System.IO.Path.Combine([| root; outputFile |])

        InjectionIO.printGenFunctions fileName1 fileName2 includeLemmas outputPath

    // Run just type equality check; used for testing
    let testTypeEq dafnyFile1 dafnyFile2 outputPath : unit =
        let reporter = initDafny

        // the main call to dafny, adapted from DafnyDriver.ProcessFiles
        let programName1 = "old"
        let mutable dafnyProgram1 = Unchecked.defaultof<Program>
        parseAST dafnyFile1 programName1 reporter &dafnyProgram1

        let programName2 = "new"
        let mutable dafnyProgram2 = Unchecked.defaultof<Program>
        parseAST dafnyFile2 programName2 reporter &dafnyProgram2

        // inspect the results
        log "***** Running typeCart"
        InjectionIO.findEqTypes (&dafnyProgram1, &dafnyProgram2)

        InjectionIO.printEqResults outputPath

    //[<EntryPoint>]
    let main (argv: string array) =
        // TODO: this whole part will be changed once this runs on folders rather than individual files
        // check the arguments
        // Dafny fails with cryptic exception if we accidentally pass an empty list of files
        if argv.Length <= 1 then
            failwith "Need to include 2 .dfy files"

        // make sure all files exist
        for a in argv do
            if not (System.IO.File.Exists(a)) then
                failwith ("file not found: " + a)

        // argv has type string array [| |], convert argv to string list []
        let argvList = argv |> Array.toList

        //we expect only two input files at the moment
        let file1 = argvList.Head
        let file2 = argvList.[1]

        let file1Path = System.IO.Path.GetFullPath(file1)
        let file2Path = System.IO.Path.GetFullPath(file2)

        let root = System.IO.Path.GetDirectoryName(file1)

        // runTypeCart expects:
        // 1. two input filenames
        // 2. an optional Extra file for map functions
        // 3. output file name
        runTypeCart file1Path file2Path root (Some "Extra.dfy") false "Combine.dfy"

        System.Console.ReadKey() |> ignore
        0
