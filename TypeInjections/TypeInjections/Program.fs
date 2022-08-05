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
        
        Typecart.typecart(oldYIL, newYIL, Utils.log).go(Typecart.DefaultTypecartOutput(outFolder))
        0
 
