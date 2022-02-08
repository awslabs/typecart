// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT

namespace TypeInjections.Test

module TestUtils =
    open Microsoft.Dafny
    open NUnit.Framework
    open System

    type TestFormat = string -> string -> unit

    let pwd (testModule: string) : string =
        let wd = Environment.CurrentDirectory

        let pd =
            System
                .IO
                .Directory
                .GetParent(
                    wd
                )
                .Parent
                .Parent
                .FullName

        System.IO.Path.Combine(
            [| pd
               "Resources"
               testModule
               TestContext.CurrentContext.Test.Name |]
        )

    let compare (actual: string) (expected: string) =
        if actual.Equals expected then
            ()
        else
            Console.WriteLine("Expected")
            Console.WriteLine(expected)
            Console.WriteLine("Actual")
            Console.WriteLine(actual)
            Assert.Fail()

    let fileCompare (actualFile: string) (expectedFile: string) =
        let expected = IO.File.ReadAllText(actualFile)

        let actual = IO.File.ReadAllText(expectedFile)

        compare actual expected

    // By convention, the test's resources are to be stored in directory
    //   Resources/<test module name>/<test name>
    let public testRunnerEq
        (testToRun: TestFormat)
        (testModule: string)
        (inputFileName1: string)
        (inputFileName2: string)
        (outputFileName: string)
        (expectedFileName: string)
        =
        let pwd = pwd testModule

        let inputFile1 =
            System.IO.Path.Combine([| pwd; inputFileName1 |])

        let inputFile2 =
            System.IO.Path.Combine([| pwd; inputFileName2 |])

        let dafnyFile1 = DafnyFile(inputFile1)
        let dafnyFile2 = DafnyFile(inputFile2)

        let outputFile =
            System.IO.Path.Combine([| pwd; outputFileName |])

        let expectedFile =
            System.IO.Path.Combine([| pwd; expectedFileName |])

        TypeInjections.Program.testTypeEq dafnyFile1 dafnyFile2 outputFile
        |> ignore

        testToRun outputFile expectedFile

    // Run the tests for generated functions
    // FilePath is synonym for string list
    // the test generator expects multiple output and expected files,
    // but the tool currently generates only one output file
    let public testRunnerGen
        (testToRun: TestFormat)
        (testModule: string)
        (inputFileName1: string)
        (inputFileName2: string)
        (extraFileName: string Option)
        (outputFileName: string)
        (expectedFileName: string)
        =
        let pwd = pwd testModule

        let inputFile1 =
            System.IO.Path.Combine([| pwd; inputFileName1 |])

        let inputFile2 =
            System.IO.Path.Combine([| pwd; inputFileName2 |])

        let outputFile =
            System.IO.Path.Combine([| pwd; outputFileName |])

        let expectedFile =
            System.IO.Path.Combine([| pwd; expectedFileName |])

        TypeInjections.Program.runTypeCart inputFile1 inputFile2 pwd extraFileName false outputFileName
        |> ignore

        testToRun outputFile expectedFile

    // run the tool to generate only the output file,
    // does not require an expected output file
    let public testRunnerOut
        (testModule: string)
        (inputFileName1: string)
        (inputFileName2: string)
        (extraFileName: string Option)
        (isInclude: bool)
        (outputFileName: string)
        (expectedFileName: string)
        =
        let pwd = pwd testModule

        let inputFile1 =
            System.IO.Path.Combine([| pwd; inputFileName1 |])

        let inputFile2 =
            System.IO.Path.Combine([| pwd; inputFileName2 |])

        let outputFile =
            System.IO.Path.Combine([| pwd; outputFileName |])

        let expectedFile =
            System.IO.Path.Combine([| pwd; expectedFileName |])


        TypeInjections.Program.runTypeCart inputFile1 inputFile2 pwd extraFileName isInclude outputFileName
        |> ignore

        fileCompare outputFile expectedFile

    let public testRunnerClass
        (testToRun: TestFormat)
        (testModule: string)
        (inputFileName: string)
        (outputFileName: string)
        (expectedFileName: string)
        =
        let pwd = pwd testModule

        let inputFile =
            System.IO.Path.Combine([| pwd; inputFileName |])

        let dafnyFile = DafnyFile(inputFile)

        let outputFile =
            System.IO.Path.Combine([| pwd; outputFileName |])

        let expectedFile =
            System.IO.Path.Combine([| pwd; expectedFileName |])

        // Run syntactic check for classes; used for testing
        // this will be removed later
        let reporter = TypeInjections.Program.initDafny

        // the main call to dafny, adapted from DafnyDriver.ProcessFiles
        let programName1 = "test"
        let mutable dafnyProgram = Unchecked.defaultof<Program>
        TypeInjections.Program.parseAST dafnyFile programName1 reporter &dafnyProgram

        TypeInjections.InjectionIO.checkClasses dafnyProgram outputFile
        |> ignore

        testToRun outputFile expectedFile
