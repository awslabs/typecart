// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT

namespace Tool

open System.Collections.Generic
open LibGit2Sharp
open System.IO
open System
open TypeInjections
open CommandLine
open TypeInjections.Typecart

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
          [<Option('i', "ignore", Required = false, HelpText = "specify filename(s) you want to ignore")>]
          ignore: seq<string>}

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
          force: bool
          [<Option('i', "ignore", Required = false, HelpText = "specify filename(s) you want to ignore")>]
          ignore: seq<string>
          }
    type ParsedOption = {oldFolder: string; newFolder: string; outFolder: string; ignore: string list}

    //NOTE 'location' refers to either the github url OR path to repo on local computer
    let checkoutCommit (hash: string) (location: string) (outputPath: string) : unit =
        //Clone = copies a repo (using a git url or local repo path) to the output directory

        try
            Repository.Clone(location, outputPath) |> ignore
        with :? LibGit2SharpException ->
            if Directory.Exists(location) then
                failwith "this location does not contain git repository"
            else
                failwith "bad URL, private or nonexistent repo"
        // get Repository object of repository copied to output directory
        let newRepo = new Repository(outputPath)
        // try to find commit user inputted in git logs
        let commitRepo = newRepo.Lookup<Commit>(hash)
        // checkout repo at given commit
        Commands.Checkout(newRepo, commitRepo) |> ignore

    let runGit (git: GitOptions) : ParsedOption =
        Utils.log "***** git commit"

        let commit1, commit2 = git.oldHash, git.newHash
        let path = git.outputFolder
        let pathOld = $"{path}/Old"
        let pathNew = $"{path}/New"
        
        let location = if git.url = null then Directory.GetCurrentDirectory() else git.url

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

        {oldFolder = pathOld;  newFolder = pathNew; outFolder = $"{path}/Output"; ignore =  (git.ignore |> Seq.toList)}

    let runLocal (local: LocalOptions) : ParsedOption =
        Utils.log "***** local project comparison"

        Utils.log $"{local.oldFolder}, {local.newFolder}, {local.outputFolder}"

        {oldFolder = local.oldFolder; newFolder = local.newFolder; outFolder = local.outputFolder; ignore = (local.ignore |> Seq.toList)}

    [<EntryPoint>]
    let main (argv: string array) =

        // command line parser stores the error in IEnumerable, need to extract
        let getError (errors: IEnumerable<Error>) : Error =
            (errors |> Seq.cast<Error> |> Seq.toList).Head

        (* ParseArguments trys to connect user input to a "verb"
         after matching to verb, returns a dictionary of option names and values
         throws error message (and returns NotParsed<obj>) for two reasons:
         1. unable to identify verb
         2. if user asks for help, method prints help message (called helperErrorMessage)
        *)
        let result =
            Parser.Default.ParseArguments<LocalOptions, GitOptions> argv

        // if verb found, result = Parsed<obj> = map of options and values
        // if no verb found or help asked for, result = NotParsed<obj> = list of error messages

        // have runGit or runLocal change value of these variables
        let input =
            match result with
            | :? (Parsed<obj>) as command ->
                match command.Value with
                | :? LocalOptions as opts -> runLocal opts
                | :? GitOptions as opts -> runGit opts
                | _ -> {oldFolder = ""; newFolder= ""; outFolder = ""; ignore = [] }
            // nothing to do if result=NotParsed<obj> because helpful error message
            // was already thrown by ParseArgument
            | :? (NotParsed<obj>) as errors ->
                // see what the error is
                match (getError errors.Errors) with
                | :? BadVerbSelectedError -> failwith $"bad verb"
                | :? HelpRequestedError -> failwith "user just wanted help!"
                | _ -> failwith "unknown error, need to investigate"
            | _ -> {oldFolder = ""; newFolder= ""; outFolder = ""; ignore = [] }


        let reporter = Utils.initDafny

        (* TypecartProject's 2nd argument can be:
        1. the absolute path to .typecartignore file
        2. a list of regex values *)
        let oldProject =
            TypecartProject(input.oldFolder, input.ignore)

        let newProject =
            TypecartProject(input.newFolder, input.ignore)

        typecart(oldProject.toYILProgram ("Old", reporter), newProject.toYILProgram ("New", reporter), Utils.log)
            .go (DefaultTypecartOutput(input.outFolder))

        0
