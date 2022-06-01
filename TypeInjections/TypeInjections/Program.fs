// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT

namespace TypeInjections

open Microsoft.Dafny
open System

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
        Console.WriteLine(dafnyPrelude)
        let dafnyPreludeDir =
            Utils.findDirectory (codebase, "dafny", "DafnyPrelude.bpl")
            |> Option.get
        logObject "found in: {0}" dafnyPreludeDir
        log "***** initialising Dafny"
        options.DafnyPrelude <- dafnyPrelude
        DafnyOptions.Install(options)
        log "***** Dafny initialised"
        reporter

    let parseAST (file: string) (programName: string) (reporter: ConsoleErrorReporter) : Program =
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
        if argv.Length < 3 then
            failwith "usage: program OLD NEW OUTPUTFOLDER"

        let argvList = argv |> Array.toList
        let oldFile = argvList.Item(0)
        let newFile = argvList.Item(1)
        let outFolder = argvList.Item(2)

        // make sure all input files exist
        for a in [oldFile;newFile] do
            if not (System.IO.File.Exists(a)) then
                failwith ("file not found: " + a)
        
        //initialise Dafny
        let reporter = initDafny

        // parse input files into Dafny programs
        log "***** calling Dafny to parse and type-check old and new file"
        let oldDafny = parseAST oldFile "Old" reporter
        let newDafny = parseAST newFile "New" reporter

        log "***** converting to YIL AST"
        log ("***** ... the old one ")
        let oldYIL = DafnyToYIL.program oldDafny
        log ("***** ... the new one ")
        let newYIL = DafnyToYIL.program newDafny

        // tests the transformation code
        Traverser.test(oldYIL)
        
        // diff the programs
        log "***** diffing the two programs"
        let diff = Differ.prog (oldYIL, newYIL)
        let diffS = (Diff.Printer()).prog diff
        Console.WriteLine(diffS)
        
        // generate translation
        log "***** generating compatibility code"
        let combine,joint = Translation.prog(oldYIL, diff)
        let transS = YIL.printer().prog(combine)
        Console.WriteLine transS

        // write output files
        log "***** writing output files"
        let writeOut fileName (prog:YIL.Program) (only: string -> bool) =
            let f = IO.Path.Combine(outFolder, fileName)
            IO.Directory.CreateDirectory(IO.Path.GetDirectoryName(f)) |> ignore
            let progF = {YIL.name = prog.name; YIL.decls = List.filter (fun (d:YIL.Decl) -> only d.name) prog.decls}
            let s = YIL.printer().prog(progF)
            IO.File.WriteAllText(f, s)
        let jointNames = List.map (fun (p:YIL.Path) -> p.name) joint
        writeOut "joint.dfy" oldYIL  (fun s -> List.contains s jointNames)
        writeOut "old.dfy" oldYIL (fun s -> not (List.contains s jointNames))
        writeOut "new.dfy" newYIL (fun s -> not (List.contains s jointNames))
        writeOut "combine.dfy" combine (fun s -> true)
        0
