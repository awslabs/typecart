// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT

namespace TypeInjections

open Microsoft.Dafny

module ProgramFR =

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
        (file: string)
        (programName: string)
        (reporter: ConsoleErrorReporter):
        Program =
        
        let dafnyFile = DafnyFile(file)
        let mutable dafnyProgram = Unchecked.defaultof<Program>
        
        logObject "***** calling Dafny parser and checker for {0}" file
        let dafnyFiles = [ dafnyFile ]

        let err =
            Main.ParseCheck(Utils.toIList dafnyFiles, programName, reporter, &dafnyProgram)

        if err <> null && err <> "" then
            failwith ("Dafny errors: " + err)
            
        dafnyProgram

    [<EntryPoint>]
    let main (argv: string array) =
        // for now, typeCart requires fully qualified paths of files
        // TODO: update to read Dafny project folder
        // check the arguments
        // Dafny fails with cryptic exception if we accidentally pass an empty list of files
        if argv.Length <= 2 then
            failwith "typeCart requires at least two input files"

        let argvList = argv |> Array.toList
        let outFolder = argvList.Head
        let files = argvList.Tail

        // make sure all input files exist
        for a in files do
            if not (System.IO.File.Exists(a)) then
                failwith ("file not found: " + a)
        
        //initialise Dafny
        let reporter = initDafny

        // parse input files
        let oldDafnyFile = parseAST (files.Item(0)) "old" reporter
        let newDafnyFile = parseAST (files.Item(1)) "old" reporter
        
        let oldYIL = DafnyToYIL.program oldDafnyFile
        let newYIL = DafnyToYIL.program newDafnyFile
        
        //let diff = Differ.prog(oldYIL, newYIL)
        //let diffS = (new Diff.Printer()).prog(diff)
        //System.Console.WriteLine(diffS)
        
        System.Console.ReadKey() |> ignore
        0
