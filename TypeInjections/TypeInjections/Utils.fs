namespace TypeInjections

open System
open System.Collections.Generic
open System.IO
open Microsoft.Dafny

module Utils =
    type Either<'a, 'b> =
        | Left of 'a
        | Right of 'b

    let fromList<'a> : List<'a> -> 'a list = Seq.toList

    // not used for the time being, but might be needed later
    let dictToMap (d: Dictionary<_, _>) : Map<_, _> = d |> Seq.map (|KeyValue|) |> Map.ofSeq

    // not used for the time being, but might be needed later
    let mapToDict (m: Map<_, _>) : Dictionary<_, _> = m :> IDictionary<_, _> |> Dictionary

    let concatList (x: List<'a>) (y: List<'a>) : List<'a> =
        let x = fromList x
        let y = fromList y
        List.append x y |> List<'a>

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
    /// l and m are disjoint
    let listDisjoint<'a when 'a: equality> (l: 'a list, m: 'a list) = listDiff (l, m) = l
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
    let listInterleave<'a> (l: 'a list, m: 'a list) =
        List.zip l m
        |> List.collect (fun (x, y) -> [ x; y ])

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

    // Prefix matcher
    let (|Prefix|_|) (pre: string) (s: string) =
        if s.StartsWith(pre) then
            Some(s.Substring(pre.Length))
        else
            None

    // Suffix matcher
    let (|Suffix|_|) (suf: string) (s: string) =
        if s.EndsWith(suf) then
            Some(s.Substring(0, s.Length - suf.Length))
        else
            None

    /// Logging utils
    let log (s: string) = Console.WriteLine(s)
    let logObject (s: string) (arg: obj) = Console.WriteLine(s, arg)


    /// Dafny utils
    let initDafny : ConsoleErrorReporter =
        // preparations, adapted from DafnyDriver.Main
        let reporter = ConsoleErrorReporter()
        let options = DafnyOptions()
        options.ApplyDefaultOptions() // needed to enable \U unicode
        // Disable module reveals / provides scopes, otherwise we get e.g. lemmas with empty bodies.
        options.DisableScopes <- true
        DafnyOptions.Install(options)
        log "***** Dafny initialised"
        reporter

    // Read in and parse a list of Dafny files
    let parseASTs (files: FileInfo list) (programName: string) (reporter: ConsoleErrorReporter) : Program =
        if List.length files = 0 then
            failwith "error: list of files supplied to parser is empty"
        let dafnyFiles = List.map (fun (x: FileInfo) -> DafnyFile x.FullName) files
        let mutable dafnyProgram = Unchecked.defaultof<Program>
        log "***** calling dafny parser for multiple files"
        let err = Main.ParseCheck(toIList dafnyFiles, programName, reporter, &dafnyProgram)
        if err <> null && err <> "" then
            failwith ("Dafny error: " + err)
        dafnyProgram

    // Read in and parse a single Dafny file
    let parseAST (file: string) (programName: string) (reporter: ConsoleErrorReporter) : Program =
        parseASTs [FileInfo(file)] programName reporter

    // detects if path is file or directory
    type SystemPathKind =
        | D of DirectoryInfo
        | F of FileInfo

    let parseSystemPath (path: string) =
        let attr = File.GetAttributes(path)

        if attr.HasFlag(FileAttributes.Directory) then
            D(DirectoryInfo(path))
        else
            F(FileInfo(path))
