// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT

namespace TypeInjections.Test

module GenFunctionTests =
    open NUnit.Framework

    type internal Marker =
        interface
        end

    let moduleName = typeof<Marker>.DeclaringType.Name
    // set the module name, alternatively we could look into determining
    // the calling module via reflection in TestUtils
    let testRunner =
        TestUtils.testRunnerGen TestUtils.fileCompare moduleName

    [<Test>]
    let SimpleDatatypeTest () =
        testRunner "Old.dfy" "New.dfy" None "Combine.dfy" "Expect.dfy"

    [<Test>]
    let RecursiveDatatypeTest () =
        testRunner "Old.dfy" "New.dfy" None "Combine.dfy" "Expect.dfy"

    [<Test>]
    let DatatypeRefTest () =
        testRunner "Old.dfy" "New.dfy" None "Combine.dfy" "Expect.dfy"

    [<Test>]
    let GenericDatatypeTest () =
        testRunner "Old.dfy" "New.dfy" None "Combine.dfy" "Expect.dfy"

    [<Test>]
    let ModuleTest () =
        testRunner "Old.dfy" "New.dfy" None "Combine.dfy" "Expect.dfy"

    [<Test>]
    let SeqTest () =
        testRunner "Old.dfy" "New.dfy" (Some "Extra.dfy") "Combine.dfy" "Expect.dfy"

    [<Test>]
    let SetTest () =
        testRunner "Old.dfy" "New.dfy" (Some "Extra.dfy") "Combine.dfy" "Expect.dfy"

    [<Test>]
    let MapTest () =
        testRunner "Old.dfy" "New.dfy" (Some "Extra.dfy") "Combine.dfy" "Expect.dfy"

    [<Test>]
    let CollectionsTest () =
        testRunner "Old.dfy" "New.dfy" (Some "Extra.dfy") "Combine.dfy" "Expect.dfy"

    [<Test>]
    let NewtypeTest () =
        testRunner "Old.dfy" "New.dfy" None "Combine.dfy" "Expect.dfy"

    [<Test>]
    let SubsetSynTest () =
        testRunner "Old.dfy" "New.dfy" (Some "Extra.dfy") "Combine.dfy" "Expect.dfy"

    [<Test>]
    let LimitTest () =
        testRunner "Old.dfy" "New.dfy" None "Combine.dfy" "Expect.dfy"
