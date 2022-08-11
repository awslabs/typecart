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
            failwith "usage: program OLD[FILE|FOLDER] NEW[FILE|FOLDER] OUTPUTFOLDER"

        let argvList = argv |> Array.toList
        let oldPath = argvList.Item(0)
        let newPath = argvList.Item(1)
        let outFolder = argvList.Item(2)

        // make sure all input paths exist
        for a in [oldPath; newPath] do
            if not (System.IO.File.Exists(a)) then
                failwith ("file not found: " + a)
        
        //initialise Dafny
        let reporter = Utils.initDafny

        // parse input files into Dafny programs
        Utils.log "***** calling Dafny to parse and type-check old and new file"
        let oldProject = Typecart.TypecartProject(oldPath)
        let newProject = Typecart.TypecartProject(newPath)
        
        Utils.log "***** calling typeCart API"
        Typecart.typecart(oldProject.toYILProgram("Old", reporter), newProject.toYILProgram("New", reporter), Utils.log)
            .go(Typecart.DefaultTypecartOutput(outFolder))
        0
 
