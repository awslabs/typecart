// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT

namespace TypeInjections

open Typecart

module Program =

    [<EntryPoint>]
    let main (argv: string array) =
        // for now, typeCart requires fully qualified paths of input files or folders
        // Dafny fails with cryptic exception if we accidentally pass an empty list of files
        
        // check and read arguments
        if argv.Length < 3 || argv.Length > 4 then
            failwith "usage: program OLD[FILE|FOLDER] NEW[FILE|FOLDER] OUTPUTFOLDER [IGNORE-PATTERNS-FILE]"
        let argvList = argv |> Array.toList
        let oldPath = argvList.Item(0)
        let newPath = argvList.Item(1)
        let outFolder = argvList.Item(2)

        // path to the file that specifies filenames to ignore when processing change.
        let ignorePatternsFile =
            if List.length argvList = 4 then
                Some(argvList.Item(3))
            else
                None

        // initialise Dafny
        let reporter = Utils.initDafny

        // initialise typecart wrappers for Dafny projects
        let oldProject = TypecartProject(oldPath, ignorePatternsFile)
        let newProject = TypecartProject(newPath, ignorePatternsFile)

        // run Dafny
        Utils.log "***** calling Dafny to parse and type-check OLD project and convert it to YIL"
        let oldYIL = oldProject.toYILProgram ("Old", reporter)
        Utils.log "***** calling Dafny to parse and type-check NEW project and convert it to YIL"
        let newYIL = newProject.toYILProgram ("New", reporter)
    
        // run typecart
        Utils.log "***** calling typeCart to produce output project"
        Typecart(oldYIL, newYIL, Utils.log).go(DefaultTypecartOutput(outFolder))

        0
