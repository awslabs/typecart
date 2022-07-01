// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT

namespace TypeInjections

open System.Collections.Generic
open System.IO
open Microsoft.Boogie
open Microsoft.Dafny
open Utils

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
    let typeDecls (prog: Program inref) : TopLevelDecl list =
        let declsOld =
            fromList prog.DefaultModuleDef.TopLevelDecls
            
        allTypeDecls declsOld
 
    // Generate the injection functions and write the result, as (syntactically) valid Dafny, to outputFile
    let printDeclarations (decls:TopLevelDecl list) (outputFilePath: string) : unit =
        let output = new StreamWriter(outputFilePath)

        let printer = Printer(output)

        printer.PrintTopLevelDecls(decls |> List<TopLevelDecl>, 2, List<IToken>(), outputFilePath)
        output.Close()