include "Old.dfy"
include "New.dfy"

  module Combine {

    import Old

    import New
    function mapMap<K, K', V, V'>(f: K -> K', g: V -> V', m: map<K, V>): map<K', V'>
      decreases m
    {
      if m == map[] then
        map[]
      else
        ghost var k: K :| k in m; ghost var v: V := m[k]; map[f(k) := g(v)] + mapMap(f, g, m - {k})
    }

    function mapMapKey<K, K', V>(f: K -> K', m: map<K, V>): map<K', V>
      decreases m
    {
      if m == map[] then
        map[]
      else
        ghost var k: K :| k in m; ghost var v: V := m[k]; map[f(k) := v] + mapMapKey(f, m - {k})
    }

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

    function seqMap<A, B>(f: A -> B, s: seq<A>): (r: seq<B>)
      ensures |s| == |r|
      decreases s
    {
      if s == [] then
        []
      else
        [f(s[0])] + seqMap(f, s[1..])
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

    function listOldToNew<T, T'>(fT: T -> T', l: Old.S.list<T>): New.S.list<T'>
      decreases l
    {
      match l
      case Cons(h: T, tl: Old.S.list<T>) =>
        New.S.list.Cons(fT(h), listOldToNew(fT, tl))
      case Nil =>
        New.S.list.Nil
    }

    function multipleCollOldToNew(m: Old.S.multipleColl): New.S.multipleColl
      decreases m
    {
      match m
      case A1(s: seq<Old.S.foo>, t: set<Old.S.list<int>>) =>
        New.S.multipleColl.A1(seqMap(fooOldToNew, s), setMap(listOldToNew, t))
      case A2(m: Old.S._Companion.ultipleColl.multipleColl) =>
        New.S.multipleColl.A2(multipleCollOldToNew(m))
      case A3(f: map<Old.S.foo, string>, x: seq<set<map<int, char>>>, y: map<Old.S.list<string>, Old.S.list<set<set<int>>>>) =>
        New.S.multipleColl.A3(mapMapKey(fooOldToNew, f), x, mapMap(listOldToNew, listOldToNew, y))
    }
  }
