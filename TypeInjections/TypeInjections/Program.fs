// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT

namespace TypeInjections

open Microsoft.Dafny

module Program =

    let log (s: string) = System.Console.WriteLine(s)
    let logObject (s: string) (arg: obj) = System.Console.WriteLine(s, arg)

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

    [<EntryPoint>]
    let main argv =
        // TODO: this whole part will be changed once this runs on folders rather than individual files
        // check the arguments
        // Dafny fails with cryptic exception if we accidentally pass an empty list of files
        if argv.Length <> 2 then
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

        let root = System.IO.Path.GetDirectoryName(file1)
        
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
        
        let typesDeclsOld = InjectionIO.typeDecls &dafnyProgram1
        let typesDeclsNew = InjectionIO.typeDecls &dafnyProgram2
        
        let outputFile1 =
            System.IO.Path.Combine([| root; "Out1.dfy" |])
        
        let outputFile2 =
            System.IO.Path.Combine([| root; "Out2.dfy" |])

        InjectionIO.printDeclarations typesDeclsOld (outputFile1: string)
        InjectionIO.printDeclarations typesDeclsNew (outputFile2: string) 
        0
