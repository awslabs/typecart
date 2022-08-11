
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT

namespace Tool

open System.IO
open System
open TypeInjections

module Tool =
    
    // based off command line flags, create and provide path for input/output folders
    let interpretFlag  (argvList: string list) =
        let flag = argvList.Item(0)
      
        // -p [inputPath] [inputPath] [outputPath]
        if flag.Contains("-p") then
          
            if argvList.Length <> 4 then
              failwith "usage: program -p OLD NEW OUTPUTFOLDER"
            
            Console.WriteLine("***** local project comparison")
          
        // -l [git commit hash] [git commit hash] [OutputPath]
        elif flag.Contains("-l") then
          
            if argvList.Length <> 4 then
              failwith "usage: program -l OLD_COMMIT NEW_COMMIT OUTPUTFOLDER"
          
            Console.WriteLine("***** git commit")
     
        // -r [github repo url] [github commit hash] [github commit hash] [OutputPath]
        elif flag.Contains("-r") then
            
            if argvList.Length <> 5 then
              failwith "usage: program -p OLD NEW OUTPUTFOLDER"
            
            Console.WriteLine("***** remote github")
          
        else failwith "flag not found please try again"
                           

    [<EntryPoint>]
    let main (argv: string array) =
        
        Utils.log "***** Entering Tool.fs"
        
        let argvList = argv |> Array.toList
        
        interpretFlag argvList 
        
        0