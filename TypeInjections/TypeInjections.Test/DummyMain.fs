
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT

namespace TypeInjections

open Microsoft.Dafny
open System.IO
open System
open TypeInjections

module Program =

    let log (s: string) = System.Console.WriteLine(s)
    let logObject (s: string) (arg: obj) = System.Console.WriteLine(s, arg)
    
    // parseAST now takes a file list
    let parseAST (files: FileInfo list) (programName: string) (reporter: ConsoleErrorReporter) : Program =
        let dafnyFiles = List.map (fun (x : FileInfo) -> DafnyFile x.FullName) files
        let mutable dafnyProgram = Unchecked.defaultof<Program>
        log "***** calling dafny parser for multiple files"
        let err =
            Main.ParseCheck(TypeInjections.Utils.toIList dafnyFiles, programName, reporter, &dafnyProgram)
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
        let codebase = TypeInjections.Utils.location
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
        fileFull[len+1..]
        
    // since YIL AST won't store '/' replace it with " "
    let giveSpace (path: string) =
        path.Replace("/", " ")
    
    let spaceToSlash (path: string) =
        path.Replace(" ", "/")
            

    /// prefixes the names of all toplevel modules
    let prefixTopDecls(prog: YIL.Program)(pref: string): YIL.Program =
        let prN (n: string) = pref + "." + n
        let prD (d: YIL.Decl) =
            match d with
            | YIL.Module(n,ds,mt) -> YIL.Module(prN n, ds, mt)
            | d -> d
        {name=prog.name; decls=List.map prD prog.decls}
        
        
    let rename (path: string) (ending: string): string =
        let endPos = path.IndexOf(".dfy")
        let newName = path.Insert( endPos, ("_" + ending ))
        newName.ToLower()
        
    let writeFile (prog: YIL.Decl) (folder:string) (prefix:string)  =
        
        let getName (x:YIL.Decl) = 
            if x.meta.position.IsNone then
                match x with
                    | YIL.Module (name, _, _) -> name + ".dfy"
                    | _ -> ".dfy"
            else
                prog.meta.position.Value.filename
        
        let outputProg = {YIL.name = getName prog; YIL.decls = [prog]}

        let progP =  prefixTopDecls outputProg prefix
        
        let endFileName = (rename outputProg.name prefix)
                
        let s = YIL.printer().prog(progP, YIL.Context(progP))
        let filePath = IO.Path.Combine(folder, endFileName)
        
        IO.File.WriteAllText(filePath, s)
        0 |> ignore
    
    
    [<EntryPoint>]
    let main (argv: string array) =
        if argv.Length < 3 then
            failwith "usage: program OLD NEW OUTPUTFOLDER"
        let argvList = argv |> Array.toList
        
        // get paths to input and outputs
        let oldFolderPath = argvList.Item(0)
        let newFolderPath = argvList.Item(1)
        let outFolderPath = argvList.Item(2)
        
        // error handling 
        for a in [oldFolderPath;newFolderPath] do
            if not (System.IO.Directory.Exists(a)) then
                failwith("folder not found:" + a)
                                
        let oldParentFolder = DirectoryInfo(oldFolderPath)
        let newParentFolder = DirectoryInfo(newFolderPath)
        
        let difFolder (oldFolder: DirectoryInfo) (newFolder: DirectoryInfo) =
            // get all files in "new" and "old" folders
            let oldFiles = oldFolder.EnumerateFiles("*.dfy", SearchOption.TopDirectoryOnly) |> Seq.toList
            let newFiles = newFolder.EnumerateFiles("*.dfy", SearchOption.TopDirectoryOnly) |> Seq.toList
            let reporter = initDafny
            
            let oldDafny = parseAST oldFiles "Old" reporter
            let newDafny = parseAST newFiles "New" reporter
            
            
            let newYIL = DafnyToYIL.program newDafny
            let oldYIL = DafnyToYIL.program oldDafny
            
           
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
            let transS = YIL.printer().prog(combine, YIL.Context(combine))
            Console.WriteLine transS
                  
            
                    // write output files
            log "***** writing output files"
            let writeOut fileName prefix (prog:YIL.Program) (only: string -> bool) =
                let folder = outFolderPath
                IO.Directory.CreateDirectory(IO.Path.GetDirectoryName(folder)) |> ignore
                // let progF = {YIL.name = prog.name; YIL.decls = List.filter (fun (d:YIL.Decl) -> only d.name) prog.decls}
                
                List.iter ( fun x -> writeFile x folder prefix) prog.decls
                
            let jointNames = List.map (fun (p:YIL.Path) -> p.name) joint
            // writeOut "joint.dfy" "Joint" oldYIL (fun s -> List.contains s jointNames)
            writeOut "joint.dfy" "Joint" oldYIL (fun s -> true)
            // writeOut "old.dfy" "Old" oldYIL (fun s -> not (List.contains s jointNames))
            // writeOut "new.dfy" "New" newYIL (fun s -> not (List.contains s jointNames))
            // writeOut "combine.dfy" "Combine" combine (fun s -> true)
            writeOut "combine.dfy" "Combine" combine (fun s -> true)
            
            
        List.iter2 (fun (x:DirectoryInfo) (y: DirectoryInfo) -> difFolder x y)
            ((oldParentFolder.GetDirectories("*", SearchOption.AllDirectories)
              |> Seq.toList) @ [oldParentFolder])
            ((newParentFolder.GetDirectories("*", SearchOption.AllDirectories)
              |> Seq.toList) @ [newParentFolder])
        
        0