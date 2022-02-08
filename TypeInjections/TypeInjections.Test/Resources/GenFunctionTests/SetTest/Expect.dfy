include "Old.dfy"
include "New.dfy"

  module Combine {

    import Old

    import New
    function setMap<T, U>(f: T --> U, s: set<T>): (res: set<U>)
      requires forall x: T :: x in s ==> f.requires(x)
      ensures |res| <= |s|
      ensures Injective(f, s) ==> |s| == |res|
      ensures res == set x: T {:trigger f(x)} {:trigger x in s} | x in s :: f(x)
      decreases s
    {
      if s == {} then
        {}
      else
        ghost var v: T :| v in s; {f(v)} + setMap(f, s - {v})
    }

    predicate Injective<T(!new), U>(f: T --> U, s: set<T>)
      requires forall x: T :: x in s ==> f.requires(x)
      decreases s
    {
      forall x: T, y: T :: 
        x in s &&
        y in s &&
        x != y ==>
          f(x) != f(y)
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

    function setOfFooOldToNew(s: Old.S.setOfFoo): New.S.setOfFoo
      decreases s
    {
      match s
      case A1(s: set<Old.S.foo>) =>
        New.S.setOfFoo.A1(setMap(fooOldToNew, s))
      case A2 =>
        New.S.setOfFoo.A2
    }

    function setOfBuiltinOldToNew(s: Old.S.setOfBuiltin): New.S.setOfBuiltin
      decreases s
    {
      match s
      case B1(s: set<int>, c: char) =>
        New.S.setOfBuiltin.B1(s, c)
      case B2(y: set<set<bool>>) =>
        New.S.setOfBuiltin.B2(y)
    }
  }
