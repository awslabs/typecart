### Example:

Given two identical modules `Old.A` and `New.A` that declare a simple datatype `foo` and a predicate `isBar`, typeCart generates a module `Combine` containing the mapping function `fooOldtoNew`. The function `fooOldtoNew`, as its name describes, converts a value of type `Old.A.foo` to the value of type `New.A.foo`. Please note that typeCart references the types by their top-level full Dafny names to avoid name clashes.

<img src="imgs/typeCart-example.png"/>

We could then easily reason about two versions of predicate `isBar` as:

<img src="imgs/proofCI.png" width="250"/>


### Features

typeCart generates functions for equivalent parametric datatypes, newtypes and subtypes of Dafny. It can also map over collection types such as sets, sequences and maps.

**Example 1: mapping function for datatype**

```dafny
  datatype option<A> =
    None
  | Some(x: A)

  function optionOldToNew<A, A'>(fA: A -> A', o: Old.M.option<A>): New.M.option<A'>
    decreases o
  {
    match o
    case None =>
      New.M.option.None
    case Some(x: A) =>
      New.M.option.Some(fA(x))
  }
```
**Example 2: mapping function for newtype:**

```dafny
  newtype int8 = x | -128 <= x < 128

  function int8OldToNew(i: Old.M.int8): (i': New.M.int8)
    ensures i as int == i' as int
    decreases i
  {
    i as int as New.M.int8
  }
```
**Example 3: mapping function for subtype:**
```dafny
  ghost const INT_MAX := 0x7fff_ffff

  type string32 = x: string | 0 <= |x| <= INT_MAX

  function string32OldToNew(s: Old.M.string32): New.M.string32
    requires 0 <= |s| <= New.M.INT_MAX
    decreases s
  {
    s
  }
```

**Example 4: mapping function for collection types:**
```dafny
  datatype collectionType<T> =
    A(a: T)
  | B(b: seq<T>)


  function seqMap<A, B>(f: A -> B, s: seq<A>): (r: seq<B>)
    ensures |s| == |r|
    decreases s
  {
    if s == [] then
      []
    else
      [f(s[0])] + seqMap(f, s[1..])
  }

  function collectionTypeOldToNew<T, T'>(fT: T -> T', c: Old.M.collectionType<T>): New.M.collectionType<T'>
    decreases c
  {
    match c
    case A(a: T) =>
      New.M.collectionType.A(fT(a))
    case B(b: seq<T>) =>
      New.M.collectionType.B(seqMap(fT, b))
  }

```

