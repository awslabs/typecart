// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT

namespace TypeInjections.Test

module IOTests =
    open NUnit.Framework

    type internal Marker =
        interface
        end

    let moduleName = typeof<Marker>.DeclaringType.Name
    // set the module name, alternatively we could look into determining
    // the calling module via reflection in TestUtils
        
    let testRunner =
        TestUtils.testRunnerGen
        
    [<Test>]
    let SimpleFolderTest () =
        testRunner "InputDirectory" "OutputDirectory"
        
        