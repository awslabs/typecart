// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT

namespace TypeInjections.Test

module ClassGenTests =
    open NUnit.Framework

    type internal Marker =
        interface
        end

    let moduleName = typeof<Marker>.DeclaringType.Name
    // set the module name, alternatively we could look into determining
    // the calling module via reflection in TestUtils
    let testRunner =
        TestUtils.testRunnerClass TestUtils.fileCompare moduleName

    [<Test>]
    let ClassTest () =
        testRunner "Test.dfy" "Output.txt" "Expect.txt"
