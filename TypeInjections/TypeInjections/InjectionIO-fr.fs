// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT

namespace TypeInjections

open System.Collections.Generic
open System.IO
open Microsoft.Boogie
open Microsoft.Dafny
open Utils
open NameUtils
open TypeEquality
open TypeInjections

// Read data from input Programs and write results out to files
// No type equality or translation logic is in this file; see TypeEquality.fs and TypeInjections.fs, respectively
module InjectionIOFR =

    // Pull out all the relevant type declarations from the program
    let private allTypeDecls : YIL.Decl list -> YIL.Decl list =
        let rec getTypeList (td: YIL.Decl) : YIL.Decl list =
            match td with
            | YIL.Decl.Datatype (name, tpvs, constructors, members, meta) ->
                [ YIL.Decl.Datatype(name, tpvs, constructors, members, meta) ]
            | YIL.Decl.Class (name, isTrait, tpvars, parent, members, meta) ->
                [ YIL.Decl.Class(name, isTrait, tpvars, parent, members, meta) ]
            | YIL.Decl.TypeDef (name, tpvars, super, predicate, isNew, meta) ->
                [ YIL.Decl.TypeDef(name, tpvars, super, predicate, isNew, meta) ]
            | YIL.Decl.Module (_, decls, _) -> List.collect getTypeList decls

        List.collect <| getTypeList


    // Find all equal types and populate the maps "same" and "diff" appropriately
    let findEqTypes (oldProg: YIL.Program, newProg: YIL.Program) : unit =
        // Make sure everything is cleared in between tests
        same.Clear()
        diff.Clear()
        oldDecls.Clear()
        newDecls.Clear()
        extraFunctionsNeeded.Clear()

        let declsOld = oldProg.decls

        let declsNew = newProg.decls

        // identify matching type declarations (by name) - use a Dictionary so we can do this in O(n)
        let namesOfNewTypes = Dictionary<string, YIL.Decl>()
        // List.iter (fun (d: YIL.Decl) -> namesOfNewTypes.Add(typeName d, d)) (allTypeDecls declsNew)

        ignore ()
