// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT

namespace TypeInjections

open System.Collections.Generic

module Utils =

    type Either<'a, 'b> =
        | Left of 'a
        | Right of 'b

    let toIList<'a> (s: 'a seq) = ResizeArray(s) :> IList<'a>

    let fromList<'a> : List<'a> -> 'a list = Seq.toList

    // Update no matter whether the key exists or not
    let updateDict<'K, 'V when 'K: equality and 'V: equality> (d: Dictionary<'K, 'V>) (k: 'K) (v: 'V) =
        if d.ContainsKey k then
            ignore (d.[k] = v)
        else
            d.Add(k, v)

    let singleList (x: 'a) : List<'a> =
        let l = List<'a>()
        l.Add(x)
        l

    // not used for the time being, but might be needed later
    let dictToMap (d: Dictionary<_, _>) : Map<_, _> = d |> Seq.map (|KeyValue|) |> Map.ofSeq

    // not used for the time being, but might be needed later
    let mapToDict (m: Map<_, _>) : Dictionary<_, _> = m :> IDictionary<_, _> |> Dictionary

    let concatList (x: List<'a>) (y: List<'a>) : List<'a> =
        let x = fromList x
        let y = fromList y
        List.append x y |> List<'a>

    // Like List.forall2, but returns false when the lengths of the lists differ
    // rather than throwing an exception
    let forallSafe (pred: 'a -> 'b -> bool) (l1: 'a list) (l2: 'b list) =
        List.length l1 = List.length l2
        && List.forall2 pred l1 l2

    let location : string =
        System.IO.Path.GetDirectoryName(
            System
                .Reflection
                .Assembly
                .GetExecutingAssembly()
                .Location
        )

    let rec findFile (currDir: string, dirName: string, fileName: string) : string option =
        if currDir = null then
            System.Console.WriteLine(sprintf "%s not found" fileName)
            None
        else
            let file =
                System.IO.Path.Combine(currDir, dirName, fileName)

            if System.IO.File.Exists(file) then
                Some file
            else
                findFile (System.IO.Path.GetDirectoryName(currDir), dirName, fileName)

    let rec findDirectory (currDir: string, dirName: string, fileName: string) : string option =
        if currDir = null then
            System.Console.WriteLine(sprintf "%s not found" fileName)
            None
        else
            let file =
                System.IO.Path.Combine(currDir, dirName, fileName)

            if System.IO.File.Exists(file) then
                Some(System.IO.Path.Combine(currDir, dirName))
            else
                findDirectory (System.IO.Path.GetDirectoryName(currDir), dirName, fileName)
