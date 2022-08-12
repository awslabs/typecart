
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT

namespace TypeInjections

open Microsoft.Dafny
open System.IO
open System
open TypeInjections

module Tester = 

    ///
    /// Write YIL ASTs to directories
    /// 
    type DirectoryOutputWriter(outFolderPath: string) =
        
        /// prefixes the names of all toplevel modules
        let prefixTopDecls(prog: YIL.Program)(pref: string): YIL.Program =
            let prN (n: string) = pref + "." + n
            let prD (d: YIL.Decl) =
                match d with
                | YIL.Module(n,ds,mt) -> YIL.Module(prN n, ds, mt)
                | d -> d
            {name=prog.name; decls=List.map prD prog.decls; meta = prog.meta}
        
                
        let writeFile (prog: YIL.Decl) (folder:string) (prefix:string)  =
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
                    prog.meta.position.Value.filename
            let outputProg = {YIL.name = getName prog; YIL.decls = [prog]; YIL.meta = prog.meta}
            let progP =  prefixTopDecls outputProg prefix
            let endFileName = (addSuffix outputProg.name prefix)
            let s = YIL.printer().prog(progP, YIL.Context(progP))
            let filePath = Path.Combine(folder, endFileName)
            IO.File.WriteAllText(filePath, s)
    
        let writeOut fileName prefix (prog:YIL.Program) =
            let folder = outFolderPath
            IO.Directory.CreateDirectory(Path.GetDirectoryName(folder)) |> ignore            
            List.iter ( fun x -> writeFile x folder prefix) prog.decls

        interface Typecart.TypecartOutput with
            member this.processOld(oldYIL: YIL.Program) = writeOut "old.dfy" "Old" oldYIL 
            member this.processNew(newYIL: YIL.Program) = writeOut "new.dfy" "New" newYIL
            member this.processJoint(jointYIL: YIL.Program) = writeOut "joint.dfy" "Joint" jointYIL 
            member this.processCombine(combineYIL: YIL.Program) = writeOut "combine.dfy" "Combine" combineYIL 

                           

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
        
        
        let outputWriter = DirectoryOutputWriter(outFolderPath)
        
        let difFolder (oldFolder: DirectoryInfo) (newFolder: DirectoryInfo) =
            // get all files in "new" and "old" folders
            let oldFiles = oldFolder.EnumerateFiles("*.dfy", SearchOption.TopDirectoryOnly) |> Seq.toList
            let newFiles = newFolder.EnumerateFiles("*.dfy", SearchOption.TopDirectoryOnly) |> Seq.toList
            let reporter = Utils.initDafny
            
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