include "Old.dfy"
include "New.dfy"

  module Combine {

    import Old

    import New
    function seqMap<A, B>(f: A -> B, s: seq<A>): (r: seq<B>)
      ensures |s| == |r|
      decreases s
    {
      if s == [] then
        []
      else
        [f(s[0])] + seqMap(f, s[1..])
    }

    function fooOldToNew(f: Old.S.foo): New.S.foo
      decreases f
    {
      match f
      case Bar(x: int) =>
        New.S.foo.Bar(x)
      case Baz(y: string) =>
        New.S.foo.Baz(y)
    }

    function seqOfFooOldToNew(s: Old.S.seqOfFoo): New.S.seqOfFoo
      decreases s
    {
      match s
      case A1(s: seq<Old.S.foo>) =>
        New.S.seqOfFoo.A1(seqMap(fooOldToNew, s))
      case A2 =>
        New.S.seqOfFoo.A2
    }

    function seqOfBuiltinOldToNew(s: Old.S.seqOfBuiltin): New.S.seqOfBuiltin
      decreases s
    {
      match s
      case B1(s: seq<int>, c: char) =>
        New.S.seqOfBuiltin.B1(s, c)
      case B2(y: seq<seq<bool>>) =>
        New.S.seqOfBuiltin.B2(y)
    }
  }
