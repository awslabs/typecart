// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT

namespace TypeInjections.Test

open System.IO
open TypeInjections
open Microsoft.Dafny

module TestUtils =
    open NUnit.Framework
    open System
    
    type Output =
    | Joint = 0
    | New = 1
    | Old = 1
    | Translations = 3
    
    let testDir : string =
        let wd = Environment.CurrentDirectory

        let pd =
            Directory
                .GetParent(
                    wd
                )
                .Parent
                .Parent
                .FullName

        Path.Combine(
            [| pd
               "Resources"
               TestContext.CurrentContext.Test.Name |]
        )
        
    let testYILCmp (filename:string)=
        let oldProj = Path.Combine([|testDir; "ExpectedDirectory"; filename|])
        let newProj = Path.Combine([|testDir; "OutputDirectory"; filename|])
        let reporter = Utils.initDafny
        let oDaf = Utils.parseAST oldProj "project" reporter
        let nDaf = Utils.parseAST newProj "project" reporter
        let oYIL = DafnyToYIL.program oDaf
        let nYIL = DafnyToYIL.program nDaf
        Utils.log $"\n\n\nold and new yil should be equal, is this true? {oYIL = nYIL}"
    
    // runs the typeCart API and produces files in the "OutputDirectory"
    let public testRunnerGen (inputDir: string) (outDir: string) =
        let reporter = Utils.initDafny
        let inputDirectory = Path.Combine([| testDir; inputDir |])
        let oldPath = Path.Combine([|inputDirectory; "Old"|])
        let newPath = Path.Combine([|inputDirectory; "New"|])
        let outFolder = Path.Combine([| testDir; outDir |])
        
        let oldProject = Typecart.TypecartProject(oldPath, None)
        let newProject = Typecart.TypecartProject(newPath, None)
        
        Typecart.typecart(oldProject.toYILProgram("Old", reporter), newProject.toYILProgram("New", reporter), Utils.log)
            .go(Typecart.DefaultTypecartOutput(outFolder))