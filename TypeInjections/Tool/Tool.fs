// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT

namespace Tool

open LibGit2Sharp
open System.IO
open System
open TypeInjections
open CommandLine

module Tool =


    [<Verb("local", HelpText = "typecart local [old project path] [new project path] [outputPath]")>]
    type LocalOptions =
        { [<Option('o', "old", Required = false, HelpText = "folder path of old project")>]
          oldFolder: string
          [<Option('n', "new", Required = false, HelpText = "folder path of new project")>]
          newFolder: string
          [<Option('p', "output", Required = false, HelpText = "path of folder to place typeCart files")>]
          outputFolder: string
          [<Option('f', "file", Required = false, HelpText = "specify filename(s) you want to run typeCart on")>]
          file: seq<string> }

    [<Verb("git", HelpText = "typecart git [old commit] [new commit] [outputPath]")>]
    type GitOptions =
        { [<Option('o', "old", Required = true, HelpText = "commit hash of old version")>]
          oldHash: string
          [<Option('n', "new", Required = true, HelpText = "commit hash of new version")>]
          newHash: string
          [<Option('p', "output", Required = true, HelpText = "path of folder to place typeCart files")>]
          outputFolder: string
          [<Option('e', "entrypoint", Required = false, HelpText = "specify the filename(s) you want to run typeCart on")>]
          file: seq<string>
          [<Option('c', "clone", Required = false, HelpText = "input a git URL")>]
          url: string
          [<Option('f', "force", Required = false, HelpText = "overwrite the Old and New folders in the Output folder")>]
          force: bool }

    //NOTE 'location' refers to either the github url OR path to repo on local computer
    let checkoutCommit (hash: string) (location: string) (outputPath: string) : unit =
        Repository.Clone(location, outputPath) |> ignore
        // get Repository object of whatever was cloned above
        let newRepo = new Repository(outputPath)
        // checkout repo at given commit
        let commitRepo = newRepo.Lookup<Commit>(hash)
        Commands.Checkout(newRepo, commitRepo) |> ignore

    let runGit (git: GitOptions) : unit =
        Utils.log "***** git commit"

        let commit1, commit2 = git.oldHash, git.newHash
        let path = git.outputFolder
        let pathOld = $"{path}/Old"
        let pathNew = $"{path}/New"

        let location =
            match git.url.Length with
            // empty git url means user wants to run typeCart in current directory
            | 0 -> Directory.GetCurrentDirectory()
            // if there is a repo URL, use it
            | _ -> Utils.log $"Path to repo is {path}"; git.url

        // lib2git needs an empty folder to store the repo clones
        for a in [ pathOld; pathNew ] do
            if Directory.Exists(a) then
                // if user lets us delete existing folder
                if git.force then
                    Directory.Delete(a, true)
                // else break program
                else
                    failwith
                        $"{a} already exists. We need an empty folder to place checkout git repo. Choose different output folder or choose --force to automatically overwrite folder data"

        checkoutCommit commit1 location pathOld
        checkoutCommit commit2 location pathNew

        Utils.log $"{pathOld}, {pathNew}, {path}/Output"


    let runLocal (local: LocalOptions) : unit =

        Utils.log "***** local project comparison"
        Utils.log $"{local.oldFolder}, {local.newFolder}, {local.outputFolder}"


    [<EntryPoint>]
    let main (argv: string array) =

        Utils.log "***** Entering Tool.fs"

        let result =
            Parser.Default.ParseArguments<LocalOptions, GitOptions> argv


        match result with
        | :? (Parsed<obj>) as command ->
            match command.Value with
            | :? LocalOptions as opts -> runLocal opts
            | :? GitOptions as opts -> runGit opts
            | _ -> ()

        | :? (NotParsed<obj>) as value -> ()
        | _ -> ()


        0
