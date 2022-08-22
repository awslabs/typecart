// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT

namespace Tool

open LibGit2Sharp
open System.IO
open System
open TypeInjections
open CommandLine

module Tool =

    //NOTE 'location' refers to either the github url OR path to repo on local computer
    let checkoutCommit (hash: string) (location: string) (outputPath: string) : unit =

        Repository.Clone(location, outputPath) |> ignore
        // get Repository object of whatever was cloned above
        let newRepo = new Repository(outputPath)
        // checkout repo at given commit
        let commitRepo = newRepo.Lookup<Commit>(hash)
        Commands.Checkout(newRepo, commitRepo) |> ignore


    type options =
        { [<Option('d', "delete", Required = false, HelpText = "use option to remove the New and Old folders")>] delete: bool
          [<Option('l', "local", Required = false, HelpText = "[old project path] [new project path] [outputPath]")>] local: seq<string>
          [<Option('g', "git", Required = false, HelpText = "[old commit] [new commit] [outputPath]")>] git: seq<string>
          [<Option('r', "remote", Required = false, HelpText = "[github repo url] [new commit] [old commit] [outputPath]")>] remote: seq<string>
          [<Option(HelpText = "Prints all messages to standard output.")>] verbose: bool
          }

    (* command line parser has group arguments into what option it is associated with
     (local option has a list of arguments that follow it, as does git and remote).
     If command line option has arguments, we need to organize arguments and run typeCart on them.
     Run typeCart only once per command line call (we can't run a remote and local project on same command line call)
     *)
    let interpretFlags  (local: string list) (git: string list) (remote: string list) : string * string * string =

        if not local.IsEmpty then
            Utils.log "***** local project comparison"
            local.[0], local.[1], local.[2]
        elif not git.IsEmpty then
            Utils.log "***** git commit"
            // location of repo
            let location = Directory.GetCurrentDirectory()

            let commit1, commit2 = git.[0], git.[1]
            let path = git.[2]
            let pathOld = $"{path}/Old"
            let pathNew = $"{path}/New"

            // lib2git needs an empty folder to store the repo clones
            for a in [ pathOld; pathNew ] do
                if Directory.Exists(a) then
                    Directory.Delete(a, true)

            checkoutCommit commit1 location pathOld
            checkoutCommit commit2 location pathNew

            pathOld, pathNew, $"{path}/Output"

        elif not remote.IsEmpty then
            Utils.log "***** remote github"

            let path = remote.[3]
            let pathOld = $"{path}/Old"
            let pathNew = $"{path}/New"
            let url = remote.[0]
            let commit1 = remote.[1]
            let commit2 = remote.[2]

            for a in [ pathOld; pathNew ] do
                if Directory.Exists(a) then
                    Directory.Delete(a, true)

            checkoutCommit commit1 url pathOld
            checkoutCommit commit2 url pathNew


            pathOld, pathNew, $"{path}/Output"

        else
            failwith "unable to read flags"
            
    // organize arguments with the flag they associated with 
    let run opt =
        let local = opt.local |> Seq.toList
        let git = opt.git |> Seq.toList
        let remote = opt.remote |> Seq.toList
        // given the list of arguments associated with each flag, run typeCart
        let oldFolder, newFolder, outputFolder = interpretFlags local git remote

        Utils.log $"old folder is {oldFolder}, new folder is {newFolder}, output folder is {outputFolder}"

    [<EntryPoint>]
    let main (argv: string array) =

        Utils.log "***** Entering Tool.fs"

        let result =
            Parser.Default.ParseArguments<options>(argv)

        //TODO get a better understanding of result
        match result with
        | :? (Parsed<options>) as parsed -> run parsed.Value
        | :? (NotParsed<'a>) as notParsed -> Utils.log $"Here is non parsed arguments {notParsed}"
        | _ as unknown -> Utils.log $"don't understand this argument {unknown}"  


        0
