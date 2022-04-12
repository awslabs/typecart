// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT

namespace TypeInjections

open System.Collections.Generic
open TypeEquality
open YIL
open TypeInjections

// Read data from input Programs and write results out to files
// No type equality or translation logic is in this file; see TypeEquality.fs and TypeInjections.fs, respectively
module InjectionIO =

    // Pull out all the relevant type declarations from the program
    let private allTypeDecls : Decl list -> Decl list =
        let rec getTypeList (td: Decl) : Decl list =
            match td with
            | Decl.Datatype (name, tpvs, constructors, members, meta) ->
                [ Decl.Datatype(name, tpvs, constructors, members, meta) ]
            | Decl.Class (name, isTrait, tpvars, parent, members, meta) ->
                [ Decl.Class(name, isTrait, tpvars, parent, members, meta) ]
            | Decl.TypeDef (name, tpvars, super, predicate, isNew, meta) ->
                [ Decl.TypeDef(name, tpvars, super, predicate, isNew, meta) ]
            | Decl.Module (_, decls, _) -> List.collect getTypeList decls
            | _ -> []

        List.collect <| getTypeList


    // Find all equal types and populate the maps "same" and "diff" appropriately
    let findEqTypes (oldProg: Program, newProg: Program) : unit =
        // Make sure everything is cleared in between tests
        same.Clear()
        diff.Clear()
        oldDecls.Clear()
        newDecls.Clear()
        extraFunctionsNeeded.Clear()

        let declsOld = oldProg.decls

        let declsNew = newProg.decls

        // identify matching type declarations (by name) - use a Dictionary so we can do this in O(n)
        let namesOfNewTypes = Dictionary<string, Decl>()
        List.iter (fun (d: Decl) -> namesOfNewTypes.Add(d.name, d)) (allTypeDecls declsNew)

        let potentialPairs =
            List.fold
                (fun acc (x: Decl) ->
                    if namesOfNewTypes.ContainsKey(x.name) then
                        (x, namesOfNewTypes.[x.name]) :: acc
                    else
                        acc)
                []
                (List.rev (allTypeDecls declsOld))

        List.iter (fun (t1, t2) -> ignore (compareTypeEq t1 t2)) potentialPairs
