// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT

namespace TypeInjections

open System.IO
open Microsoft.Dafny
open System.Collections.Generic
open NameUtilsFR
open Utils
open YIL

// Before generating injections, we want to determine which types are equal and which are not. This module
// contains that logic.
module TypeEqualityFR =
    
    // We want to memoize the computation so that we don't need to compute the result multiple times if a type is
    // referenced in other types. Using mutable state is cleaner than passing around sets everywhere
    let same : HashSet<string> = HashSet<string>()
    let diff : HashSet<string> = HashSet<string>()

    // Stores the decls for each type that we know is equal, since we will need to reference these decls later
    let oldDecls : Dictionary<string, Decl> = Dictionary<string, Decl>()
    let newDecls : Dictionary<string, Decl> = Dictionary<string, Decl>()

    // Compare two types for equivalence - this is the only function external callers need to know about
    let public compareTypeEq (t1: Decl) (t2: Decl) : bool = false
