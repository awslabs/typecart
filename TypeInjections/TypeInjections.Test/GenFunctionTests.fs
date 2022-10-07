// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT

namespace TypeInjections.Test

module GenFunctionTests =
    open NUnit.Framework

    type internal Marker =
        interface
        end
        
    let testRunner =
        TestUtils.testRunnerGen
        
    [<Test>]
    let SimpleDatatypeTest () =
        testRunner "InputDirectory" "OutputDirectory"
        
    [<Test>]
    let RecursiveDatatypeTest () =
        testRunner "InputDirectory" "OutputDirectory"

    [<Test>]
    let DatatypeRefTest () =
        testRunner "InputDirectory" "OutputDirectory"

    [<Test>]
    let GenericDatatypeTest () =
        testRunner "InputDirectory" "OutputDirectory"

    [<Test>]
    let ResultTest () =
        testRunner "InputDirectory" "OutputDirectory"

    [<Test>]
    let SeqTest () =
        testRunner "InputDirectory" "OutputDirectory"

    [<Test>]
    let SetTest () =
        testRunner "InputDirectory" "OutputDirectory"

    [<Test>]
    let MapTest () =
        testRunner "InputDirectory" "OutputDirectory"

    [<Test>]
    let CollectionsTest () =
        testRunner "InputDirectory" "OutputDirectory"

    [<Test>]
    let NewtypeTest () =
        testRunner "InputDirectory" "OutputDirectory"

    [<Test>]
    let SubsetSynTest () =
        testRunner "InputDirectory" "OutputDirectory"

    [<Test>]
    let LimitTest () =
        testRunner "InputDirectory" "OutputDirectory"

        
        