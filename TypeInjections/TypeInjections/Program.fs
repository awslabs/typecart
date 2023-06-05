// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT

namespace TypeInjections

open Typecart

module Program =

    [<EntryPoint>]
    let main (argv: string array) =
        // for now, typeCart requires fully qualified paths of input files or folders
        // check the arguments
        // Dafny fails with cryptic exception if we accidentally pass an empty list of files
        if argv.Length < 3 then
            failwith "usage: program OLD[FILE|FOLDER] NEW[FILE|FOLDER] OUTPUTFOLDER"

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

        // parse input files into Dafny programs
        Utils.log "***** calling Dafny to parse and type-check old and new file"

        let oldProject =
            TypecartProject(oldPath, ignorePatternsFile)

        let newProject =
            TypecartProject(newPath, ignorePatternsFile)

        Utils.log "***** calling typeCart API"

        let oldYIL =
            oldProject.toYILProgram ("Old", reporter)

        let newYIL =
            newProject.toYILProgram ("New", reporter)

        typecart(oldYIL, newYIL, Utils.log)
            .go (DefaultTypecartOutput(outFolder))

        0
