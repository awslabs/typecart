// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT

namespace TypeInjections

open Microsoft.Dafny
open System.IO
open System

module Program =

    let log (s: string) = System.Console.WriteLine(s)
    let logObject (s: string) (arg: obj) = System.Console.WriteLine(s, arg)
    
    // parseAST now takes a file list
    let parseAST (files: FileInfo list) (programName: string) (reporter: ConsoleErrorReporter) : Program =
        let dafnyFiles = List.map (fun (x : FileInfo) -> DafnyFile x.FullName) files
        let mutable dafnyProgram = Unchecked.defaultof<Program>
        log "***** calling dafny parser for multiple files"
        let err =
            Main.ParseCheck(Utils.toIList dafnyFiles, programName, reporter, &dafnyProgram)
        if err <> null && err <> "" then
            failwith ("Dafny error: " + err)
        dafnyProgram

    let initDafny : ConsoleErrorReporter =
        // preparations, adapted from DafnyDriver.Main
        let reporter = ConsoleErrorReporter()
        let options = DafnyOptions()
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
 
    // get relative path of file
    let getRelative (oldFolder : string) (fileFull: string) : string =
        let len = oldFolder.Length
        fileFull[len..]

 (*
    Note: from dev-io, to be removed later 

    [<EntryPoint>]
    let main (argv: string array) =
        // Dafny fails with cryptic exception if we accidentally pass an empty list of files
        
        // ------------------- adding my part ---------------------
        
        // need: Old folder, New folder, Output folder
        if argv.Length < 3 then
            failwith "usage: program OLD NEW OUTPUTFOLDER"

        // get path to old and new folders
        let argvList = argv |> Array.toList
        let oldFolderPath = argvList.Item(0)
        let newFolderPath = argvList.Item(1)
        let outputFolder = argvList.Item(2)
        
        // ensure folders exist in system
        for a in [oldFolderPath;newFolderPath] do
            if not (System.IO.Directory.Exists(a)) then
                failwith("folder not found:" + a)
                
        // grab folder objects given path
        let oldFolder = DirectoryInfo(oldFolderPath)
        let newFolder = DirectoryInfo(newFolderPath)
        
        // get all files in old and new folder
        let oldFiles = oldFolder.EnumerateFiles("*.dfy", SearchOption.AllDirectories) |> Seq.toList
        let newFiles = newFolder.EnumerateFiles("*.dfy", SearchOption.AllDirectories) |> Seq.toList

        //initialise Dafny
        let reporter = initDafny
      
        // get list of dafny programs from input files
        let oldDafny = List.map (fun (x : FileInfo) -> parseAST [x] ("Old" + x.Name) reporter) oldFiles
        let newDafny = List.map (fun (x : FileInfo) -> parseAST [x] "New" reporter) newFiles
          
        // printing out renamed module files
        let printWithDaf (prog: Program) (fileName: string) =
            
            //TODO print in correct structure
            let path = outputFolder + "/"  + prog.Name
            
            // building printer obj
            let output = new StreamWriter(path )
            let printer = Printer(output)
            // getting all modules, functions, and objects
            let decls = prog.DefaultModuleDef.TopLevelDecls
         
           
            // iterate through decls => string print modules, else use dafny printer
            let rec printLine (vals : TopLevelDecl list) (prefix : string): unit =
                for (a:TopLevelDecl) in vals do
                    match a with
                    | :? LiteralModuleDecl as d ->   output.WriteLine("module " + prefix + "." + d.Name + "{"); printLine (d.ModuleDef.TopLevelDecls |> Seq.toList) prefix; output.WriteLine("}")
                    | :? _ ->  printer.PrintTopLevelDecls(Collections.Generic.List([a]), 2, Collections.Generic.List<Microsoft.Boogie.IToken>(), path)
            // call printLine function with given modules and other declarations, prefix will be "old"
            printLine (decls |> Seq.toList) "Old"
            // need to flush (program breaks if left out)
            output.Flush()
              
        // call printDaf function
        List.iter2 (fun (x: Program) (y: FileInfo) -> printWithDaf x y.FullName) oldDafny oldFiles
        
        //NOTE onto step 2: Read all files again and parse (now we read from output file)
        // read in files now that modules have New. and Old.
        // let rewrittenOldFiles = getAllFiles (IO.DirectoryInfo(argvList.Item(0)))
        // let rewrittenNewFiles = getAllFiles (IO.DirectoryInfo(argvList.Item(1)))

        
        //QUESTION do we parse Old and New files together since they have different module names?
        // let rewrittenOldDafny = parseAST oldFiles "Old" reporter 
        // let rewrittenNewDafny = parseAST newFiles "New" reporter
        
        //NOTE onto step 3, strip Old/New from module names
        

        0
        // -------------------ending my part ----------------------------------
        
 *)      

    /// prefixes the names of all toplevel modules
    let prefixTopDecls(prog: YIL.Program)(pref: string): YIL.Program =
        let prN (n: string) = pref + "." + n
        let prD (d: YIL.Decl) =
            match d with
            | YIL.Module(n,ds,mt) -> YIL.Module(prN n, ds, mt)
            | d -> d
        {name=prog.name; decls=List.map prD prog.decls}
    
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
        let oldDafny = parseAST [FileInfo(oldFile)] "Old" reporter
        let newDafny = parseAST [FileInfo(newFile)] "New" reporter

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
        let writeOut fileName prefix (prog:YIL.Program) (only: string -> bool) =
            let f = IO.Path.Combine(outFolder, fileName)
            IO.Directory.CreateDirectory(IO.Path.GetDirectoryName(f)) |> ignore
            let progF = {YIL.name = prog.name; YIL.decls = List.filter (fun (d:YIL.Decl) -> only d.name) prog.decls}
            let progP = prefixTopDecls progF prefix
            let s = YIL.printer().prog(progP)
            IO.File.WriteAllText(f, s)
        let jointNames = List.map (fun (p:YIL.Path) -> p.name) joint
        writeOut "joint.dfy" "Joint" oldYIL (fun s -> List.contains s jointNames)
        writeOut "old.dfy" "Old" oldYIL (fun s -> not (List.contains s jointNames))
        writeOut "new.dfy" "New" newYIL (fun s -> not (List.contains s jointNames))
        writeOut "combine.dfy" "Combine" combine (fun s -> true)
        0
