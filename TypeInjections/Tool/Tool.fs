// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT

namespace Tool

open System.Collections.Generic
open LibGit2Sharp
open System.IO
open TypeInjections
open CommandLine

module Tool =

    //TODO add 'entryPoint' option to local and git
    [<Verb("local", IsDefault = true, HelpText = "typecart local [old project path] [new project path] [outputPath]")>]
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
          [<Option('c', "clone", Required = false, HelpText = "input a git URL")>]
          url: string
          [<Option('f', "force", Required = false, HelpText = "overwrite the Old and New folders in the Output folder")>]
          force: bool }

    let checkInputs (paths: string list) =
        for p in paths do
            // ensure folders are in computer
            if not (Directory.Exists(p)) then
                failwith $"{p} is not found"
            // make sure folder has at least 1 dafny file
            let dafnyFiles = Directory.GetFiles(p, "*.dfy")

            if dafnyFiles.Length = 0 then
                failwith $"{p} does not contain any dafny files"

    //NOTE 'location' refers to either the github url OR path to repo on local computer
    let checkoutCommit (hash: string) (location: string) (outputPath: string) : unit =
        try
            Repository.Clone(location, outputPath) |> ignore
        with :? LibGit2SharpException ->
            if Directory.Exists(location) then
                failwith "this location does not contain git repository"
            else
                failwith "bad URL, private or nonexistent repo"
        // get the Repository object of repository copied to output directory
        let newRepo = new Repository(outputPath)
        // try to find the commit that user inputted in git logs
        let commitRepo = newRepo.Lookup<Commit>(hash)
        // checkout the repo at the given commit
        Commands.Checkout(newRepo, commitRepo) |> ignore
        // ensure that the checked out repo has dafny file(s)
        checkInputs [ outputPath ]

    let runGit (git: GitOptions) : unit =
        Utils.log "***** git commit"

        let commit1, commit2 = git.oldHash, git.newHash
        let path = git.outputFolder
        let pathOld = $"{path}/Old"
        let pathNew = $"{path}/New"

        let location =
            match git.url.Length with
            // empty git url means the user wants to run typeCart in current directory
            | 0 -> Directory.GetCurrentDirectory()
            // if there is a repo URL, use it
            | _ ->
                Utils.log $"Path to repo is {path}"
                git.url

        // lib2git needs an empty folder to store the repo clones
        for a in [ pathOld; pathNew ] do
            if Directory.Exists(a) then
                // if the user lets us delete existing folder
                if git.force then
                    Directory.Delete(a, true)
                // else break program
                else
                    failwith
                        $"{a} already exists. We need an empty folder to place checkout git repo.
                        Choose different output folder or choose --force to automatically overwrite folder data"

        checkoutCommit commit1 location pathOld
        checkoutCommit commit2 location pathNew

        checkInputs [ pathNew; pathOld ]

        Program.main [| pathOld
                        pathNew
                        $"{path}/Output" |]
        |> ignore

        Utils.log $"{pathOld}, {pathNew}, {path}/Output"

    let runLocal (local: LocalOptions) : unit =
        Utils.log "***** local project comparison"

        checkInputs [ local.oldFolder
                      local.newFolder ]

        if not (Directory.Exists(local.outputFolder)) then
            failwith "Could not find directory"

        Utils.log $"{local.oldFolder}, {local.newFolder}, {local.outputFolder}"

        Program.main [| local.oldFolder
                        local.newFolder
                        local.outputFolder |]
        |> ignore

    [<EntryPoint>]
    let main (argv: string array) =
        // command line parser stores the error in IEnumerable, need to extract
        let getError (errors: IEnumerable<Error>) : Error =
            (errors |> Seq.cast<Error> |> Seq.toList).Head

        (*
         ParseArguments connects the user input to a "verb",
         returns a dictionary of option names and values,
         throws error message (and returns NotParsed<obj>) for two reasons:
           1. unable to identify verb
           2. if user asks for help, method prints help message (called helperErrorMessage)
        *)
        let result =
            Parser.Default.ParseArguments<LocalOptions, GitOptions> argv

        // if verb found, result = Parsed<obj> = map of options and values
        // if no verb found or help asked for, result = NotParsed<obj> = list of error messages
        match result with
        | :? (Parsed<obj>) as command ->
            match command.Value with
            | :? LocalOptions as opts -> runLocal opts
            | :? GitOptions as opts -> runGit opts
            | _ -> ()
        // nothing to do if result=NotParsed<obj> because helpful error message
        // was already thrown by ParseArgument
        | :? (NotParsed<obj>) as errors ->
            // see what the error is
            match (getError errors.Errors) with
            | :? BadVerbSelectedError -> failwith $"bad verb"
            | :? HelpRequestedError -> failwith "user just wanted help!"
            | _ -> failwith "unknown error, need to investigate"
        | _ -> ()

        0
