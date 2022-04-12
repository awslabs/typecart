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

    // Run the tests for generated functions
    // FilePath is synonym for string list
    // the test generator expects multiple output and expected files,
    // but the tool currently generates only one output file
    let public testRunnerGen
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

        let outputFile =
            System.IO.Path.Combine([| pwd; outputFileName |])

        let expectedFile =
            System.IO.Path.Combine([| pwd; expectedFileName |])

        TypeInjections.Program.main [| outputFile
                                       inputFile1
                                       inputFile2 |]
        |> ignore

        testToRun outputFile expectedFile
