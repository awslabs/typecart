namespace TypeInjections

// Dafny
open Microsoft.Dafny

// a barebones main program for testing - should be merged with the existing Program.fs
module ProgramFR =
    
    module Utils = UtilsFR

    let private log (s: string) = System.Console.WriteLine(s)

    /// Directory of the running program
    let private codebase = Utils.location

    let private runDafny sources =
        // preparations, adapted from DafnyDriver.Main
        let reporter = ConsoleErrorReporter()
        let dafnyOptions = DafnyOptions(reporter)
        dafnyOptions.WarnShadowing <- true
        log ("***** searching for DafnyPrelude.bpl")
        (* Dafny initialization always call Boogie initialization, which depends on loading DafnyPrelude.bpl, a Boogie file
           implementing the Dafny built-ins. Even though we will not run Boogie, we need to go through this step.
           But Dafny cannot find the file in dafny/Binaries because it uses the location of the current program to locate it.
           So we copy the file into the current project and point Dafny to it.
        *)

        // A lazy version of `Option.orElse dflt opt` that computes `dflt` only if `opt == None`.
        // This is used to avoid calling `Utils.findFile` once the file has been found.
        let orElse (dflt: 'a option Lazy) (opt: 'a option) : 'a option =
            if Option.isSome opt then
                opt
            else
                dflt.Force()

        let dafnyPrelude =
            // When using the binary installation of Dafny:
            Utils.findFile (codebase, "dafny", "DafnyPrelude.bpl")
            // When using Dafny built from source:
            |> orElse (lazy (Utils.findFile (codebase, "dafny/Binaries", "DafnyPrelude.bpl")))
            |> Option.get

        dafnyOptions.DafnyPrelude <- dafnyPrelude
        DafnyOptions.Install(dafnyOptions)
        log ("  found")

        // the main call to dafny, adapted from DafnyDriver.ProcessFiles
        let programName = "yucca"
        let mutable dafnyProgram = Unchecked.defaultof<Program>
        // the first part of the dafny computation
        log ("***** calling Dafny parser and checker")

        let err =
            Main.ParseCheck(Utils.toIList sources, programName, reporter, &dafnyProgram)

        if not (isNull err) && err <> "" then
            failwithf "Dafny errors: %s" err

        // we skip the remaining parts: Translate (translation to boogie), Boogie (boogie verification), and Compile (output generation)

        dafnyProgram

    let private dafnyToYIL dafnyProgram =
        log "***** traversing Dafny AST"
        DafnyToYIL.program dafnyProgram

    [<EntryPoint>]
    let main argv =
        // check the arguments
        // Dafny fails with cryptic exception if we accidentally pass an empty list of files
        if argv.Length <= 1 then
            failwith "empty list of arguments"

        let argvList = argv |> Array.toList

        let outFolder = argvList.Head
        let files = argvList.Tail

        // make sure all files exist
        for a in files do
            if not (System.IO.File.Exists(a)) then
                failwith ("file not found: " + a)

        // process files
        let oldFile = DafnyFile (files.Item(0))
        let newFile = DafnyFile (files.Item(1))
        let oldDafny = runDafny [oldFile]
        let oldYIL = DafnyToYIL.program oldDafny
        let newDafny = runDafny [newFile]
        let newYIL = DafnyToYIL.program newDafny
        
        let diff = Differ.prog(oldYIL, newYIL)
        
        let diffS = (new Diff.Printer()).prog(diff)
        System.Console.WriteLine(diffS)
        0
