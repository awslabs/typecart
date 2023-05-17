// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT

namespace TypeInjections.Test

open System.IO
open TypeInjections
open Microsoft.Dafny

module TestUtils =
    open NUnit.Framework
    open System
    module T = Typecart
    
    type TestFormat = string -> string -> unit
    
    let pwd : string =
        let wd = Environment.CurrentDirectory

        let pd =
            Directory
                .GetParent(
                    wd
                )
                .Parent
                .Parent
                .FullName

        Path.Combine(
            [| pd
               "Resources"
               TestContext.CurrentContext.Test.Name |]
        )

    type DirectoryOutputWriter(outFolderPath: string) =
                        
        let writeFile (prog: YIL.Program) (folder:string) (prefix:string)  =
            let addSuffix (path: string) (ending: string): string =
                let endPos = path.IndexOf(".dfy")
                let newName = path.Insert( endPos, ("_" + ending ))
                newName.ToLower()
            let getName (x:YIL.Decl) =
                if x.meta.position.IsNone then
                    match x with
                        | YIL.Module (name, _, _) -> name + ".dfy"
                        | _ -> ".dfy"
                else
                    x.meta.position.Value.filename
            
            
            let mods = List.filter (fun (x:YIL.Decl) -> x.meta.position.IsSome) prog.decls
            // if YIL.decl is empty, don't write anything
            if mods.Length = 0 then
                0 |> ignore
            else
                
                let outputProg = {YIL.name = getName mods.Head; YIL.decls = prog.decls; YIL.meta = YIL.emptyMeta}
                let endFileName = (addSuffix outputProg.name prefix)
                let s = YIL.printer().prog(outputProg, YIL.Context(outputProg))
                let filePath = Path.Combine(folder, endFileName)
                IO.File.WriteAllText(filePath, s)
    
        let writeOut fileName prefix (prog:YIL.Program) =
            let folder = outFolderPath
            
            writeFile prog folder prefix

        interface Typecart.TypecartOutputProcessor with
            member this.processOld(oldYIL: YIL.Program) = writeOut "old.dfy" "Old" oldYIL 
            member this.processNew(newYIL: YIL.Program) = writeOut "new.dfy" "New" newYIL
            member this.processJoint(jointYIL: YIL.Program) = writeOut "joint.dfy" "Joint" jointYIL 
            member this.processCombine(translationsYIL: YIL.Program) =
                writeOut "combine.dfy" "Combine" translationsYIL  
                           
    let typeCartAPI (argv: string array) =
        
        Utils.log "***** Entering typecartAPI"
        
        if argv.Length < 3 then
            failwith "usage: program OLD NEW OUTPUTFOLDER"
        let argvList = argv |> Array.toList
        
        // get paths to input and outputs
        let oldFolderPath = argvList.Item(0)
        let newFolderPath = argvList.Item(1)
        let outFolderPath = argvList.Item(2)
        
        // is there a typecartignore file?
        let tcIgnore =
            if argvList.Length > 3 then Some (argvList.Item(3)) else None
        
        
        Directory.CreateDirectory(outFolderPath) |> ignore
        
        // error handling 
        for a in [oldFolderPath;newFolderPath;outFolderPath] do
            if not (Directory.Exists(a)) then
                failwith("folder not found:" + a)
                                
        let oldProj = T.TypecartProject(DirectoryInfo(oldFolderPath), tcIgnore)
        let newProj = T.TypecartProject(DirectoryInfo(newFolderPath), tcIgnore)
        
        let outputWriter = DirectoryOutputWriter(outFolderPath)
        
        T.Typecart(oldProj.toYILProgram("Old", Utils.initDafny),
                   newProj.toYILProgram("New", Utils.initDafny)).go(outputWriter)
       
    let public testRunnerGen (directoryName: string) (outputDirectoryName: string) =
        let inputDirectory = Path.Combine([| pwd; directoryName |])
        let inputDirectoryOld = Path.Combine([|inputDirectory; "Old"|])
        let inputDirectoryNew = Path.Combine([|inputDirectory; "New"|])
        let outputDirectory = Path.Combine([| pwd; outputDirectoryName |])
        typeCartAPI [|inputDirectoryOld; inputDirectoryNew; outputDirectory|]   
    
    (* 
    let public testRunnerGen
        (testToRun: TestFormat)
        (inputFileName1: string)
        (inputFileName2: string)
        (outputFileName: string)
        (expectedFileName: string)
        =
        let inputFile1 =
            Path.Combine([| pwd; inputFileName1 |])

        let inputFile2 =
            Path.Combine([| pwd; inputFileName2 |])

        let outputFile =
            Path.Combine([| pwd; outputFileName |])

        let expectedFile =
            Path.Combine([| pwd; expectedFileName |])

        TypeInjections.Program.runTypeCart inputFile1 inputFile2 pwd extraFileName false outputFileName
        |> ignore

        testToRun outputFile expectedFile
    *)