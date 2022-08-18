// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT

namespace TypeInjections.Test

open System.IO
open TypeInjections
open Microsoft.Dafny

module TestUtils =
    open NUnit.Framework
    open System

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
            let rest = List.filter (fun (x:YIL.Decl) -> x.meta.position.IsNone) prog.decls
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

        interface Typecart.TypecartOutput with
            member this.processOld(oldYIL: YIL.Program) = writeOut "old.dfy" "Old" oldYIL 
            member this.processNew(newYIL: YIL.Program) = writeOut "new.dfy" "New" newYIL
            member this.processJoint(jointYIL: YIL.Program) = writeOut "joint.dfy" "Joint" jointYIL 
            member this.processCombine(combineYIL: YIL.Program) = writeOut "combine.dfy" "Combine" combineYIL  
                           
    let typeCartAPI (argv: string array) =
        
        Utils.log "***** Entering typecartAPI"
        
        if argv.Length < 3 then
            failwith "usage: program OLD NEW OUTPUTFOLDER"
        let argvList = argv |> Array.toList
        
        // get paths to input and outputs
        let oldFolderPath = argvList.Item(0)
        let newFolderPath = argvList.Item(1)
        let outFolderPath = argvList.Item(2)
        
        Directory.CreateDirectory(outFolderPath) |> ignore
        
        // error handling 
        for a in [oldFolderPath;newFolderPath;outFolderPath] do
            if not (Directory.Exists(a)) then
                failwith("folder not found:" + a)
                                
        let oldParentFolder = DirectoryInfo(oldFolderPath)
        let newParentFolder = DirectoryInfo(newFolderPath)
        
        let outputWriter = DirectoryOutputWriter(outFolderPath)
        
        let difFolder (oldFolder: DirectoryInfo) (newFolder: DirectoryInfo) =
            // get all files in "new" and "old" folders
            let oldFiles = oldFolder.EnumerateFiles("*.dfy", SearchOption.TopDirectoryOnly) |> Seq.toList
            let newFiles = newFolder.EnumerateFiles("*.dfy", SearchOption.TopDirectoryOnly) |> Seq.toList
            
            let reporter = Utils.initDafny
            
            Utils.logObject "here are oldFiles {0}" oldFiles
            Utils.logObject "here are newFiles {0}" newFiles
            
            let oldDafny = Utils.parseASTs oldFiles "Old" reporter
            let newDafny = Utils.parseASTs newFiles "New" reporter
            
            let newYIL = DafnyToYIL.program newDafny
            let oldYIL = DafnyToYIL.program oldDafny
            
            let typecart = Typecart.typecart(oldYIL, newYIL, Utils.log)
            
            typecart.go(outputWriter)
        
        List.iter2 (fun (x:DirectoryInfo) (y: DirectoryInfo) -> difFolder x y)
            ((oldParentFolder.GetDirectories("*", SearchOption.AllDirectories)
              |> Seq.toList) @ [oldParentFolder])
            ((newParentFolder.GetDirectories("*", SearchOption.AllDirectories)
              |> Seq.toList) @ [newParentFolder])
        
        0
        
    let public testRunnerGen
        (directoryName: string)
        (outputDirectoryName: string)
        =

        let inputDirectory =
            Path.Combine([| pwd; directoryName |])

        let inputDirectory1 = Path.Combine([|inputDirectory; "Old"|])
        let inputDirectory2 = Path.Combine([|inputDirectory; "New"|])
        
        let outputDirectory =
            Path.Combine([| pwd; outputDirectoryName |])

        typeCartAPI [|inputDirectory1; inputDirectory2; outputDirectory|] |> ignore 
        
        0 |> ignore