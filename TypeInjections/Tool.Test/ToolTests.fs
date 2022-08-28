namespace Tool.Test

open System
open System.IO
open TestUtils
open Tool


module IOTests =
    open NUnit.Framework



    [<Test>]
    // --old input is missing
    let MissingRequiredOption () =
        // since --old is missing, rest of args don't matter. Program breaks beforehand
        let input =
            $"local --new {resourcePath}/New -p {resourcePath}/Output"
        let args = input.Split(" ")
        Assert.Catch(fun () -> Tool.main args |> ignore) |> ignore
        //TODO assert type of error is correct

    [<Test>]
    // no dafny files given in input
    let NoDafnyTest () =
        // folder has only txt file
        let argsTxt = [ $"{resourcePath}/Local/NoDafnyTest/OnlyText" ]
        Assert.Catch(fun () -> Tool.checkInputs argsTxt) |> ignore
        //TODO assert type of error is correct
        
        // folder is empty
        let argsEmpty = [ $"{resourcePath}/Local/NoDafnyTest/Empty" ]
        Assert.Catch(fun () -> Tool.checkInputs argsEmpty) |> ignore
        //TODO assert type of error is correct


    [<Test>]
    // with correct inputs, typecart local works
    let LocalGoodInput () =
        let input =
            $"local --old {resourcePath}/Local/GoodInput/Old --new {resourcePath}/Local/GoodInput/New -p {resourcePath}/Local/GoodInput/Output"

        let args = input.Split(" ")
        Tool.main args |> ignore
        // ensure 4 files are printed out with correct filenames, since input is good
        let outputFilenames =
            List.map
                (fun (x: string) -> FileInfo(x).Name)
                (Directory.GetFiles($"{resourcePath}/Local/GoodInput/Output")
                 |> Seq.toList)

        let expectedFilenames =
            List.map
                (fun (x: string) -> FileInfo(x).Name)
                (Directory.GetFiles($"{resourcePath}/Local/GoodInput/Expected")
                 |> Seq.toList)

        Assert.AreEqual(outputFilenames, expectedFilenames)



    [<Test>]
    // ensure long commit hashes work on remote
    let GitLongHashTest () =

        // clear out old output
        if Directory.Exists($"{resourcePath}/Git/LongHashTest/Output") then
            Directory.Delete($"{resourcePath}/Git/LongHashTest/Output", true)

        Tool.checkoutCommit "12e27596be07f3b386f558aa6485473339badd95" "https://github.com/tschuerl/DafnyExample.git" $"{resourcePath}/Git/LongHashTest/Output/New"
        Tool.checkoutCommit "0f836ae9a38334a7def8d5f3c1ff5941ab0cc109" "https://github.com/tschuerl/DafnyExample.git" $"{resourcePath}/Git/LongHashTest/Output/Old"
        cmpFiles $"{resourcePath}/Git/LongHashTest/Expected" $"{resourcePath}/Git/LongHashTest/Output"


    [<Test>]
    // Can we clone remote repo based on short hash (first 7 characters)
    let GitShortHashTest () =
        // clear out old output
        if Directory.Exists($"{resourcePath}/Git/ShortHashTest/Output") then
            Directory.Delete($"{resourcePath}/Git/ShortHashTest/Output", true)

        Tool.checkoutCommit "12e2759" "https://github.com/tschuerl/DafnyExample.git" $"{resourcePath}/Git/ShortHashTest/Output/New"
        Tool.checkoutCommit "0f836a" "https://github.com/tschuerl/DafnyExample.git" $"{resourcePath}/Git/ShortHashTest/Output/Old"
        cmpFiles $"{resourcePath}/Git/ShortHashTest/Expected" $"{resourcePath}/Git/ShortHashTest/Output"


    [<Test>]
    // can we get commits from dif branches
    let GitDifBranchHashTest () =
        // clear out old output
        if Directory.Exists($"{resourcePath}/Git/DifBranchHashTest/Output") then
            Directory.Delete($"{resourcePath}/Git/DifBranchHashTest/Output", true)
            
        Tool.checkoutCommit "0f836ae" "https://github.com/tschuerl/DafnyExample.git" $"{resourcePath}/Git/DifBranchHashTest/Output/Old"
        Tool.checkoutCommit "6734af6" "https://github.com/tschuerl/DafnyExample.git" $"{resourcePath}/Git/DifBranchHashTest/Output/New"
        cmpFiles $"{resourcePath}/Git/DifBranchHashTest/Expected" $"{resourcePath}/Git/DifBranchHashTest/Output"

    [<Test>]
    // raise exception for bad git URL
    let GitBadURLTest () =
        Assert.Catch
            (fun () ->
                Tool.checkoutCommit "0f836ae" "https://github.com/tschuerl/IMAGINARY_REPO.git" $"{resourcePath}/Git/BadURLTest/Output")
        |> ignore


    [<Test>]
    // no repository / bad repository in directory
    let GitBadLocation () =
        // no git repo
        let exn =
            Assert.Catch(fun () -> Tool.checkoutCommit "0f836ae" $"{resourcePath}/Git/BadLocation" $"{resourcePath}/Git/BadLocation/Generated")

        Console.WriteLine $"Exn was: {exn.Message}"
        // git repo has no dafny files
        
        (* TODO ask Matthias how to replicate local git repo in unit testing (git wanted me to make a submodule)
        let outFolder = $"{resourcePath}/Git/BadLocation/Generated/Output"
        // ensure output directory is empty (in Tool.fs, other method handles this, checkout needs this to be done manually)
        if Directory.Exists(outFolder) then
            Directory.Delete(outFolder, true)

        let exnNoDafny =
            Assert.Catch(fun () -> Tool.checkoutCommit "20e447" $"{resourcePath}/Git/BadLocation/RepoNoDafny" outFolder)

        Console.WriteLine $"Exn was: {exnNoDafny.Message}" *)

    [<Test>]
    // user called unsupported verb
    let BadVerb () =
        // oldPath, newPath, outPath don't matter program fails beforehand
        let input =
            $"badVerb --old {resourcePath}/Old --new {resourcePath}/New -p {resourcePath}/Output"

        let args = input.Split(" ")

        Assert.Catch(fun () -> Tool.main args |> ignore)
        |> ignore

    [<Test>]
    let EnsureHelp () =
        // general help
        Assert.Catch(fun () -> Tool.main [| "--help" |] |> ignore)
        |> ignore
        // help for certain verb
        Assert.Catch(fun () -> Tool.main [| "local"; "--help" |] |> ignore)
        |> ignore
