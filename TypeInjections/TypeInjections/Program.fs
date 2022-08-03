
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
        (* Dafny initialization always call Boogie initialization, which depends on loading DafnyPrelude.bpl, a Boogie file
               implementing the Dafny built-ins. Even though we will not run Boogie, we need to go through this step.
               But Dafny cannot find the file in dafny/Binaries because it uses the location of the current program to locate it.
               So we copy the file into the current project and point Dafny to it.
            *)
        // get the directory of the running program
        DafnyOptions.Install(options)
        log "***** Dafny initialised"
        reporter
 
    // get relative path of file/folder -> fileFull = a/b/c/d.dfy, parentFolder = a/b, output = c/d.dfy
    let getRelative (parentFolder : string) (fileFull: string) : string =
        let len = parentFolder.Length
        fileFull[len..]

    // prefixes the names of all toplevel modules
    let prefixTopDecls(prog: YIL.Program)(pref: string): YIL.Program =
        let prN (n: string) = pref + "." + n
        let prD (d: YIL.Decl) =
            match d with
            | YIL.Module(n,ds,mt) -> YIL.Module(prN n, ds, mt)
            | d -> d
        {name=prog.name; decls=List.map prD prog.decls}
        
    // appends 'ending' to filename
    let rename (path: string) (ending: string): string =
        let endPos = path.IndexOf(".dfy")
        let newName = path.Insert( endPos, ("_" + ending ))
        newName.ToLower()
        
    
    let writeFile (prog: YIL.Decl) (folder:string) (prefix:string)  =
        
        let getName (x:YIL.Decl) =
            // for combine YIL, meta info "file name" is empty. Go to module in YIL and retrieve name 
            if x.meta.position.IsNone then
                match x with
                    | YIL.Module (name, _, _) -> name + ".dfy"
                    | _ -> ".dfy"
            // other YIL have filename available
            else
                prog.meta.position.Value.filename
        
        
        let outputProg = {YIL.name = getName prog; YIL.decls = [prog]}
        let progP =  prefixTopDecls outputProg prefix
        let endFileName = (rename outputProg.name prefix)
                
        let s = YIL.printer().prog(progP)
        let filePath = IO.Path.Combine(folder, endFileName)
        
        IO.File.WriteAllText(filePath, s)
        0 |> ignore
        
    let writeOut fullPath prefix (prog:YIL.Program) (only: string -> bool) =
        IO.Directory.CreateDirectory(fullPath) |> ignore
        List.iter ( fun x -> writeFile x fullPath prefix) prog.decls
        
        
    // rename files from project and output them, no files in other project to compare against
    let noDiff (files: FileInfo list) prefix (path:string) =
        let reporter = initDafny
        let Dafny = parseAST files prefix reporter
        let YIL = DafnyToYIL.program Dafny
        writeOut path prefix YIL (fun s -> true)
        
        
    // finding the difference
    let difFolder (oldFiles: FileInfo list) (newFiles: FileInfo list) (path:string) =
        // get all files in "new" and "old" folders
        let reporter = initDafny
        
        // get Dafny AST of new and old files
        let oldDafny = parseAST oldFiles "Old" reporter
        let newDafny = parseAST newFiles "New" reporter
        
        // convert dafny ast to yil ast
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
        let transS = YIL.printer().prog(combine)
        Console.WriteLine transS
              
        
        // write output files
        log "***** writing output files"

            
        //TODO jointNames not working properly
        let jointNames = List.map (fun (p:YIL.Path) -> p.name) joint
        // writeOut relativePath "Joint" oldYIL (fun s -> List.contains s jointNames)
        writeOut path "Joint" oldYIL (fun s -> true)
        writeOut path "Old" oldYIL (fun s -> not (List.contains s jointNames))
        writeOut path "New" newYIL (fun s -> not (List.contains s jointNames))
        writeOut path "Combine" combine (fun s -> true)
        
        
        
    // grab all visible folder, ignore the Hidden ones (ie .git or .vscode)
    let allVisibleDir (parent: DirectoryInfo) :  string list =
        // helper function checks if folder properties contain the word hidden
        let (|Hidden|_|)  (s:string) =
            if s.Contains("Hidden") then
                Some(s)
            else
                None
        
        let rec getDirList (dir: DirectoryInfo)  : string list =
            // if dir has attribute "Hidden" don't include in list, others include in list and dive into
            match dir.Attributes.ToString() with
                |  Hidden rest -> []
                | _ -> [getRelative parent.FullName dir.FullName] @ List.collect getDirList (dir.GetDirectories("*", SearchOption.TopDirectoryOnly) |> Seq.toList)
                
        getDirList parent
        

    
    [<EntryPoint>]
    let main (argv: string array) =
        if argv.Length < 3 then
            failwith "usage: program OLD NEW OUTPUTFOLDER"
        let argvList = argv |> Array.toList
        
        // get paths to input and output folders
        let oldFolderPath = argvList.Item(0)
        let newFolderPath = argvList.Item(1)
        let outFolderPath = argvList.Item(2)
        
        // error handling 
        for a in [oldFolderPath;newFolderPath] do
            if not (System.IO.Directory.Exists(a)) then
                failwith("folder not found:" + a)
                
                
        let oldParentFolder = DirectoryInfo(oldFolderPath)
        let newParentFolder = DirectoryInfo(newFolderPath)

        // check out each folder, if there are files from Old and New to compare, do so. Else if folder is only present in one project, simply rename file and print out
        let runComparision (possRelPath: string)  =
            let possOldFolder = DirectoryInfo(oldFolderPath + possRelPath)
            let possNewFolder = DirectoryInfo(newFolderPath + possRelPath)
            
            let outputPath = outFolderPath + possRelPath
            
            // error handling if one project doesn't have given folder
            let oldFiles =
                try
                    possOldFolder.EnumerateFiles("*.dfy", SearchOption.TopDirectoryOnly) |> Seq.toList
                with
                    | :? DirectoryNotFoundException -> logObject "****** No files in {0} for old project" possRelPath; []
                    
            let newFiles =
                try
                    possNewFolder.EnumerateFiles("*.dfy", SearchOption.TopDirectoryOnly) |> Seq.toList
                with
                    | :? DirectoryNotFoundException -> logObject "****** No files in {0} for old project" possRelPath; []

            
            
            
            if newFiles.IsEmpty && oldFiles.IsEmpty then
                log "***** Folder has no files in New or Old Project"
                0 |> ignore
            // if one folder doesn't have any files in given path, print out files in other path
            else if newFiles.IsEmpty then
                log "***** newFiles is empty"
                noDiff oldFiles "Old" outputPath
            else if oldFiles.IsEmpty then
                log "***** oldFiles is empty"
                noDiff newFiles "New" outputPath
            // if there are files to compare between projects
            else
                difFolder oldFiles newFiles outputPath
                
            0 |> ignore
          
          
          
        // get all possible relative folder paths in new and old, get list of all unique folder paths and then compare the files in these folders
        let newRel = allVisibleDir newParentFolder
        let oldRel = allVisibleDir oldParentFolder 
        let relDir = (Seq.distinct (newRel @ oldRel)) |> Seq.toList
        
        List.iter (fun (x:string) -> runComparision x) relDir 
        
        0