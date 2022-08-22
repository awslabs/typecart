// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT

namespace Tool

open LibGit2Sharp
open System.IO
open System
open TypeInjections

module Tool =

    //NOTE 'location' refers to either the github url OR path to repo on local computer
    let checkoutCommit (hash: string) (location: string) (outputPath: string) : unit =
        Utils.log $"path to repo is {outputPath}"

        Repository.Clone(location, outputPath) |> ignore
        // get Repository object of whatever was cloned above
        let newRepo = new Repository(outputPath)
        // checkout repo at given commit
        let commitRepo = newRepo.Lookup<Commit>(hash)
        Commands.Checkout(newRepo, commitRepo) |> ignore

    // based off command line flags, create and provide path for input/output folders
    let interpretFlag (argvList: string list) =
        let flag = argvList.Item(0)

        // -p [inputPath] [inputPath] [outputPath]
        if flag.Contains("-p") then
            Console.WriteLine("***** local project comparison")

            if argvList.Length <> 4 then
                failwith "usage: program -p OLD NEW OUTPUTFOLDER"

        // -l [git commit hash] [git commit hash] [OutputPath]
        elif flag.Contains("-l") then
            Console.WriteLine("***** git commit")

            if argvList.Length <> 4 then
                failwith "usage: program -l OLD_COMMIT NEW_COMMIT OUTPUTFOLDER"

            // location of repo
            let location = Directory.GetCurrentDirectory()

            let commit1 = argvList.Item(1)
            let commit2 = argvList.Item(2)

            let path = argvList.Item(3)
            let pathOld = $"{path}/Old"
            let pathNew = $"{path}/New"

            // lib2git needs an empty folder to store the repo clones
            for a in [ pathOld; pathNew ] do
                if Directory.Exists(a) then
                    Directory.Delete(a, true)

            checkoutCommit commit1 location pathOld
            checkoutCommit commit2 location pathNew


        // -r [github repo url] [github commit hash] [github commit hash] [OutputPath]
        elif flag.Contains("-r") then

            Console.WriteLine("***** remote github")

            if argvList.Length <> 5 then
                failwith "usage: program -r GITHUB_URL OLD_COMMIT NEW_COMMIT OUTPUTFOLDER"

            let url = argvList.Item(1)

            let commit1 = argvList.Item(2)
            let commit2 = argvList.Item(3)

            let path = argvList.Item(4)
            let pathOld = $"{path}/Old"
            let pathNew = $"{path}/New"

            // lib2git requires an empty folder to place repos
            for a in [ pathOld; pathNew ] do
                if Directory.Exists(a) then
                    Directory.Delete(a, true)

            // grab repos of new and old projects
            checkoutCommit commit1 url pathOld
            checkoutCommit commit2 url pathNew

        else
            failwith "flag not found please try again"


    [<EntryPoint>]
    let main (argv: string array) =

        Utils.log "***** Entering Tool.fs"
        let argvList = argv |> Array.toList
        interpretFlag argvList
        0
