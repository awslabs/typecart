// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT

namespace Tool.Test

open System.IO
open NUnit.Framework

module TestUtils =

    let wd = System.Environment.CurrentDirectory

    let pd =

        Directory.GetParent(wd).Parent.Parent.FullName

    let resourcePath = Path.Combine([| pd; "Resources" |])
    
        // compare text in files between output and expected
    let cmpFiles (path1: string) (path2: string) =
        // get all files from output and expected
        let expected =
            DirectoryInfo(path1)
                .GetFiles("*.dfy", SearchOption.AllDirectories)
            |> Seq.toList

        let output =
            DirectoryInfo(path2)
                .GetFiles("*.dfy", SearchOption.AllDirectories)
            |> Seq.toList
        // get text out of cloned repo and expected repo
        let expectedText =
            List.map (fun (x: FileInfo) -> x.OpenText().ReadToEnd()) expected

        let outputText =
            List.map (fun (x: FileInfo) -> x.OpenText().ReadToEnd()) output

        List.iter2 (fun (x: string) (y: string) -> Assert.AreEqual(x, y)) expectedText outputText
