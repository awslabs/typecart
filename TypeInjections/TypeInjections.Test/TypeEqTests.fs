// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT

namespace TypeInjections.Test

module TypeEqTests =
    open NUnit.Framework

    type internal Marker =
        interface
        end

    let moduleName = typeof<Marker>.DeclaringType.Name
    // set the module name, alternatively we could look into determining
    // the calling module via reflection in TestUtils
    let testRunner =
        TestUtils.testRunnerEq TestUtils.fileCompare moduleName

    [<Test>]
    let DatatypeTest () =
        testRunner "Old.dfy" "New.dfy" "Combine.txt" "Expect.txt"
    // Type injection tool requires input filenames in title-case
    // output filenames are title-case too for consistency
    [<Test>]
    let ModuleTest () =
        testRunner "Old.dfy" "New.dfy" "Combine.txt" "Expect.txt"

    [<Test>]
    let LengthTest () =
        testRunner "Old.dfy" "New.dfy" "Combine.txt" "Expect.txt"

    [<Test>]
    let OrderTest () =
        testRunner "Old.dfy" "New.dfy" "Combine.txt" "Expect.txt"

    [<Test>]
    let NewtypeTest () =
        testRunner "Old.dfy" "New.dfy" "Combine.txt" "Expect.txt"

    [<Test>]
    let SynonymTest () =
        testRunner "Old.dfy" "New.dfy" "Combine.txt" "Expect.txt"

    [<Test>]
    let SubsetTest () =
        testRunner "Old.dfy" "New.dfy" "Combine.txt" "Expect.txt"

    [<Test>]
    let ClassTest () =
        testRunner "Old.dfy" "New.dfy" "Combine.txt" "Expect.txt"
