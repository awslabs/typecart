namespace TypeInjections

open System.Collections.Generic

// FR: copying over my Utils file from YuccaDafnyCompiler, this should be merged into the one here
module UtilsFR =
    /// conversions between C# and F# collection types
    let toIList<'a> (s: 'a seq) = ResizeArray(s) :> IList<'a>
    /// conversions between C# and F# collection types
    let fromIList<'a> (s: IList<'a>) = Seq.toList (s :> 'a seq)

    /// a list except for the last element
    let listDropLast<'a> (l: 'a list) = l.GetSlice(Some 0, Some(l.Length - 2))
    /// last element of a list
    let listLast<'a> (l: 'a list) = l.Item(l.Length - 1)
    /// true if duplicate entries in list
    let listHasDuplicate<'a when 'a: equality> (l: 'a list) = (List.distinct l).Length <> l.Length
    /// l without m
    let listDiff<'a when 'a: equality> (l: 'a list, m: 'a list) =
        List.filter (fun x -> not (List.contains x m)) l
    /// number of occurrences of a value in a list
    let listCount<'a when 'a: equality> (l: 'a list, x: 'a) = (List.filter (fun u -> u = x) l).Length
    /// list as string with given separator
    let listToString<'a> (l: 'a list, sep: string) =
        String.concat sep (List.map (fun x -> x.ToString()) l)

    let stringToList (s: string, sep: string) : string list = s.Split(sep) |> List.ofArray

    /// apply a map given as a list of pairs
    let listmap<'a, 'b when 'a: equality> (l: ('a * 'b) list, x: 'a) =
        Option.map (fun (_, b) -> b) (List.tryFind (fun (a, _) -> a = x) l)
    /// build a list by alternating elements from two lists of the same length
    let listInterleave<'a>(l: 'a list, m: 'a list) = List.zip l m |> List.collect (fun (x,y) -> [x;y])

    // find file 'name' in directory 'dir' or an ancestor, used to find DafnyPrelude.bpl
    let rec findFile (currDir: string, dirName: string, fileName: string) : string option =
        if currDir = null then
            None
        else
            let file =
                System.IO.Path.Combine(currDir, dirName, fileName)

            if System.IO.File.Exists(file) then
                Some file
            else
                findFile (System.IO.Path.GetDirectoryName(currDir), dirName, fileName)

    let location : string =
        System.IO.Path.GetDirectoryName(
            System
                .Reflection
                .Assembly
                .GetExecutingAssembly()
                .Location
        )

    // Like List.forall2, but returns false when the lengths of the lists differ
    // rather than throwing an exception
    let forallSafe (pred: 'a -> 'b -> bool) (l1: 'a list) (l2: 'b list) =
        List.length l1 = List.length l2
        && List.forall2 pred l1 l2

    // Update no matter whether the key exists or not
    let updateDict<'K, 'V when 'K: equality and 'V: equality> (d: Dictionary<'K, 'V>) (k: 'K) (v: 'V) =
        if d.ContainsKey k then
            ignore (d.[k] = v)
        else
            d.Add(k, v)
