// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT

namespace TypeInjections

open Microsoft.Dafny
open System

module Program =
    
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
        let reporter = Utils.initDafny

        // parse input files into Dafny programs
        Utils.log "***** calling Dafny to parse and type-check old and new file"
        let oldDafny = Utils.parseAST oldFile "Old" reporter
        let newDafny = Utils.parseAST newFile "New" reporter

        Utils.log "***** converting to YIL AST"
        Utils.log ("***** ... the old one ")
        let oldYIL = DafnyToYIL.program oldDafny
        Utils.log ("***** ... the new one ")
        let newYIL = DafnyToYIL.program newDafny

        // tests the transformation code
        Traverser.test(oldYIL)
        
        // diff the programs
        Utils.log "***** diffing the two programs"
        let diff = Differ.prog (oldYIL, newYIL)
        let diffS = (Diff.Printer()).prog diff
        Console.WriteLine(diffS)
        
        // generate translation
        Utils.log "***** generating compatibility code"
        let combine,joint = Translation.prog(oldYIL, diff)
        let transS =
            let combine = Analysis.AnalyzeModuleImports().prog(combine) in
                YIL.printer().prog(combine, YIL.Context(combine))
        Console.WriteLine transS
        
        // write output files
        Utils.log "***** writing output files"
        
        let writeOut fileName (prog:YIL.Program) (fp: Analysis.Pipeline) =
            let f = IO.Path.Combine(outFolder, fileName)
            IO.Directory.CreateDirectory(IO.Path.GetDirectoryName(f)) |> ignore
            let progF = fp.apply(prog)
            let s =YIL.printer().prog(progF, YIL.Context(progF))
            IO.File.WriteAllText(f, s)
        
        let jointNames = List.map (fun (p:YIL.Path) -> p.name) joint
        let processOld: Traverser.Transform list = [
                    Analysis.mkFilter(fun s -> not (List.contains s jointNames))
                    Analysis.PrefixNotFoundImportsWithJoint()
                    Analysis.PrefixTopDecls("Old")
                    Analysis.ImportJointInOldNew()
                    Analysis.AnalyzeModuleImports()]
        let processNew: Traverser.Transform list = [
                    Analysis.mkFilter(fun s -> not (List.contains s jointNames))
                    Analysis.PrefixNotFoundImportsWithJoint()
                    Analysis.PrefixTopDecls("New")
                    Analysis.ImportJointInOldNew()
                    Analysis.AnalyzeModuleImports()]
        let processJoint: Traverser.Transform list = [
                    Analysis.mkFilter(fun s -> List.contains s jointNames)
                    Analysis.PrefixTopDecls("Joint")
                    Analysis.AnalyzeModuleImports()]
        let processCombine: Traverser.Transform list = [
                    Analysis.mkFilter(fun _ -> true)
                    Analysis.PrefixTopDecls("Combine")
                    Analysis.ImportInCombine()
                    Analysis.AnalyzeModuleImports()]
        
        let (~~) arg = arg |> Analysis.Pipeline
        
        writeOut "joint.dfy" oldYIL ~~processJoint
        writeOut "old.dfy" oldYIL ~~processOld
        writeOut "new.dfy" newYIL ~~processNew
        writeOut "combine.dfy" combine ~~processCombine
        0
 