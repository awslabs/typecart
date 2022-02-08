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
module InjectionIO =

    // Pull out all the relevant type declarations from the program
    let private allTypeDecls : TopLevelDecl list -> TopLevelDecl list =
        let rec getTypeList (td: TopLevelDecl) : TopLevelDecl list =
            match td with
            | :? DatatypeDecl as d -> [ d ]
            | :? NewtypeDecl as n -> [ n ]
            | :? TypeSynonymDecl as t -> [ t ]
            | :? LiteralModuleDecl as d -> List.collect getTypeList (fromList d.ModuleDef.TopLevelDecls)
            | :? ClassDecl as c ->
                // We can safely ignore _default class for each module as such classes are not used in Dafny programs.
                // They are there only to collect various AST nodes in the Dafny implementation.
                if c.Name = "_default" then
                    []
                else
                    [ c ]
            | _ -> []

        List.collect <| getTypeList

    // Find all equal types and populate the maps "same" and "diff" appropriately
    let findEqTypes (oldProg: Program inref, newProg: inref<Program>) : unit =
        // Make sure everything is cleared in between tests
        same.Clear()
        diff.Clear()
        oldDecls.Clear()
        newDecls.Clear()
        extraFunctionsNeeded.Clear()

        let declsOld =
            fromList oldProg.DefaultModuleDef.TopLevelDecls

        let declsNew =
            fromList newProg.DefaultModuleDef.TopLevelDecls

        // identify matching type declarations (by name) - use a Dictionary so we can do this in O(n)
        let namesOfNewTypes = Dictionary<string, TopLevelDecl>()
        List.iter (fun (d: TopLevelDecl) -> namesOfNewTypes.Add(typeName d, d)) (allTypeDecls declsNew)

        let potentialPairs =
            List.fold
                (fun acc (x: TopLevelDecl) ->
                    let name = typeName x

                    if namesOfNewTypes.ContainsKey(name) then
                        (x, namesOfNewTypes.[name]) :: acc
                    else
                        acc)
                []
                (List.rev (allTypeDecls declsOld))

        List.iter (fun (t1, t2) -> ignore (compareTypeEq t1 t2)) potentialPairs

    // For collection types, we need to add extra functions to map the type constructors over the collections.
    // We include those functions in a separate file and simply parse and store the AST. This is much easier
    // than generating the AST manually.
    let parseExtraFunctions (p: Program) : unit =
        let decls =
            fromList p.DefaultModuleDef.TopLevelDecls

        let findFunction (m: MemberDecl) : unit =
            match m with
            | :? Function as f ->
                if not (extraFunctions.ContainsKey(f.Name)) then
                    extraFunctions.Add(f.Name, f)
            | _ -> ()

        let rec findAllFunctions (t: TopLevelDecl) : unit =
            match t with
            | :? DefaultClassDecl as d -> List.iter findFunction (fromList d.Members)
            | :? LiteralModuleDecl as l -> List.iter findAllFunctions (fromList l.ModuleDef.TopLevelDecls)
            | _ -> ()

        List.iter findAllFunctions decls

    let checkClasses (prog: Program) (outputFilePath: string) : unit =
        let allClassDecls : TopLevelDecl list -> ClassDecl list =
            let rec getClassList (td: TopLevelDecl) : ClassDecl list =
                match td with
                | :? LiteralModuleDecl as d -> List.collect getClassList (fromList d.ModuleDef.TopLevelDecls)
                | :? ClassDecl as c ->
                    if c.Name = "_default" then
                        []
                    else
                        [ c ]
                | _ -> []

            List.collect <| getClassList

        let allClassDecls =
            allClassDecls (fromList prog.DefaultModuleDef.TopLevelDecls)

        let supported : HashSet<string> = HashSet<string>()
        let unsupported : HashSet<string> = HashSet<string>()

        List.iter
            (fun (c: ClassDecl) ->
                if synCheckClass c then
                    ignore (supported.Add(typeName c))
                else
                    ignore (unsupported.Add(typeName c)))
            allClassDecls

        let output = new StreamWriter(outputFilePath)
        output.WriteLine("OK CLASSES")
        output.WriteLine("-----------")
        let sameList = fromList (List<string>(supported))
        List.iter (fun (s: string) -> output.WriteLine s) sameList
        output.Write('\n')
        output.WriteLine("NOT OK CLASSES")
        output.WriteLine("---------------")
        let diffList = fromList (List<string>(unsupported))
        List.iter (fun (s: string) -> output.WriteLine s) diffList
        output.Close()

    // Generate the injection functions and write the result, as (syntactically) valid Dafny, to outputFile
    let printGenFunctions oldFileName newFileName includeLemmas (outputFilePath: string) : unit =
        let output = new StreamWriter(outputFilePath)
        // TODO: will need to include more than 2 files eventually
        output.WriteLine("include \"" + oldFileName + "\"")
        output.WriteLine("include \"" + newFileName + "\"")
        // name for the lemma file is hardcoded right now, as we will generate lemmas later
        if includeLemmas then
            output.WriteLine("include \"Lemmas.dfy\"")

        let printer = Printer(output)

        let decls =
            singleList (genOuter includeLemmas :> TopLevelDecl)

        printer.PrintTopLevelDecls(decls, 2, List<IToken>(), outputFilePath)
        output.Close()

    // Print the equal and non-equal types appearing in both files, used for testing
    let printEqResults (outputFilePath: string) : unit =
        let output = new StreamWriter(outputFilePath)
        output.WriteLine("EQUAL TYPES")
        output.WriteLine("-----------")
        let sameList = fromList (List<string>(same))
        List.iter (fun (s: string) -> output.WriteLine s) sameList
        output.Write('\n')
        output.WriteLine("NON-EQUAL TYPES")
        output.WriteLine("---------------")
        let diffList = fromList (List<string>(diff))
        List.iter (fun (s: string) -> output.WriteLine s) diffList
        output.Close()
