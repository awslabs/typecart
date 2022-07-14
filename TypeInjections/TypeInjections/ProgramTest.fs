
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT

namespace TypeInjections

open Microsoft.Dafny
open System.IO
open System

module ProgramTest =

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
        if argv.Length < 3 then
            failwith "usage: program OLD NEW OUTPUTFOLDER"
        let argvList = argv |> Array.toList
        let oldFolderPath = argvList.Item(0)
        let newFolderPath = argvList.Item(1)
        let outputFolder = argvList.Item(2)
        
        for a in [oldFolderPath;newFolderPath] do
            if not (System.IO.Directory.Exists(a)) then
                failwith("folder not found:" + a)
                
        let oldFolder = DirectoryInfo(oldFolderPath)
        let newFolder = DirectoryInfo(newFolderPath)
        
        let oldFiles = oldFolder.EnumerateFiles("*.dfy", SearchOption.AllDirectories) |> Seq.toList
        let newFiles = newFolder.EnumerateFiles("*.dfy", SearchOption.AllDirectories) |> Seq.toList
        let reporter = initDafny
      
        let oldDafny = List.map (fun (x : FileInfo) -> parseAST [x] ("Old" + x.Name) reporter) oldFiles
        let newDafny = List.map (fun (x : FileInfo) -> parseAST [x] "New" reporter) newFiles
          
        let printWithDaf (prog: Program) (fileName: string) =    
            //TODO print in correct structure
            let path = outputFolder + "/"  + prog.Name
            
            let output = new StreamWriter(path )
            let printer = Printer(output)
            let decls = prog.DefaultModuleDef.TopLevelDecls
         
           
            let rec printLine (vals : TopLevelDecl list) (prefix : string): unit =
                for (a:TopLevelDecl) in vals do
                    match a with
                    | :? LiteralModuleDecl as d ->   output.WriteLine("module " + prefix + "." + d.Name + "{"); printLine (d.ModuleDef.TopLevelDecls |> Seq.toList) prefix; output.WriteLine("}")
                    | :? _ ->  printer.PrintTopLevelDecls(Collections.Generic.List([a]), 2, Collections.Generic.List<Microsoft.Boogie.IToken>(), path)
            printLine (decls |> Seq.toList) "Old"
            output.Flush()
              
        List.iter2 (fun (x: Program) (y: FileInfo) -> printWithDaf x y.FullName) oldDafny oldFiles
        0