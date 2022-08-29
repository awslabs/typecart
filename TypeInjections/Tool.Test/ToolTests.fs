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

        Assert.Catch(fun () -> Tool.main args |> ignore)
        |> ignore
    //TODO assert type of error is correct

    [<Test>]
    // no dafny files given in input
    let NoDafnyTest () =
        // folder has only txt file
        let argsTxt =
            [ $"{resourcePath}/Local/NoDafnyTest/OnlyText" ]

        Assert.Catch(fun () -> Tool.checkInputs argsTxt)
        |> ignore
        //TODO assert type of error is correct

        // folder is empty
        let argsEmpty =
            [ $"{resourcePath}/Local/NoDafnyTest/Empty" ]

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

    //TODO test long commit hashes

    //TODO test short commit hashes
    
    //TODO test commits not from "main"
    
    //TODO test typecart git --clone <URL>

    [<Test>]
    // raise exception for bad git URL
    let GitBadURLTest () =
        Assert.Catch
            (fun () ->
                Tool.checkoutCommit
                    "0f836ae"
                    "https://github.com/awslabs/IMAGINARY_REPO.git"
                    $"{resourcePath}/Git/BadURLTest/Output")
        |> ignore

    [<Test>]
    // no repository / bad repository in directory
    let GitBadLocation () =
        // no git repo
        let exn =
            Assert.Catch
                (fun () ->
                    Tool.checkoutCommit
                        "0f836ae"
                        $"{resourcePath}/Git/BadLocation"
                        $"{resourcePath}/Git/BadLocation/Generated")

        Console.WriteLine $"Exn was: {exn.Message}"

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
