// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT

namespace TypeInjections

open System.Collections.Generic
open Microsoft.Boogie
open Microsoft.Dafny

// Handles the logic for generating the type injection functions as AST nodes
module TypeInjections =

    // For a few parts in the translation process (for now, for mapping type translations over sequences, sets, and maps),
    // we want to include extra functions in the output file. It is easiest to read them and store them as AST nodes
    // from an extra input file. The following map and set store the parsed ASTs and determine which we need to include
    // in the output.
    let extraFunctions = Dictionary<string, Function>()
    let extraFunctionsNeeded = HashSet<string>()
