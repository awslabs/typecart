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

    function mapMapValue<K, V, V'>(f: V -> V', m: map<K, V>): (m': map<K, V'>)
      requires forall k: K :: k in m.Keys ==> f.requires(m[k])
      ensures m.Keys == m'.Keys
      ensures |m| == |m'|
      decreases m
    {
      ghost var result: map<K, V'> := map k: K {:trigger m[k]} {:trigger k in m} | k in m :: f(m[k]);
      assert |result.Keys| == |result|;
      result
    }

    function mapMapKey<K, K', V>(f: K -> K', m: map<K, V>): map<K', V>
      decreases m
    {
      if m == map[] then
        map[]
      else
        ghost var k: K :| k in m; ghost var v: V := m[k]; map[f(k) := v] + mapMapKey(f, m - {k})
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

    function mapFooKeyOldToNew(m: Old.S.mapFooKey): New.S.mapFooKey
      decreases m
    {
      match m
      case A1(s: map<Old.S.foo, int>) =>
        New.S.mapFooKey.A1(mapMapKey(fooOldToNew, s))
      case A2 =>
        New.S.mapFooKey.A2
    }

    function mapFooValOldToNew(m: Old.S.mapFooVal): New.S.mapFooVal
      decreases m
    {
      match m
      case B1(s: map<bool, Old.S.foo>) =>
        New.S.mapFooVal.B1(mapMapValue(fooOldToNew, s))
      case B2 =>
        New.S.mapFooVal.B2
    }

    function mapFooBothOldToNew(m: Old.S.mapFooBoth): New.S.mapFooBoth
      decreases m
    {
      match m
      case C1(m: map<Old.S.foo, Old.S.foo>) =>
        New.S.mapFooBoth.C1(mapMap(fooOldToNew, fooOldToNew, m))
      case C3 =>
        New.S.mapFooBoth.C3
    }

    function optionOldToNew<T, T'>(fT: T -> T', o: Old.S.option<T>): New.S.option<T'>
      decreases o
    {
      match o
      case None =>
        New.S.option.None
      case Some(x: T) =>
        New.S.option.Some(fT(x))
    }

    function typOldToNew<T, T'>(fT: T -> T', t: Old.S.typ<T>): New.S.typ<T'>
      decreases t
    {
      match t
      case D0(st: Old.S.option<T>) =>
        New.S.typ.D0(optionOldToNew(fT, st))
      case D1(s: Old.S.option<string>) =>
        New.S.typ.D1(optionOldToNew((x: string) => x, s))
      case D2(f: Old.S.typ<T>) =>
        New.S.typ.D2(typOldToNew(fT, f))
      case D3(g: Old.S.typ<string>) =>
        New.S.typ.D3(typOldToNew((x: string) => x, g))
      case D4(t: Old.S.option<Old.S.option<string>>) =>
        New.S.typ.D4(optionOldToNew(t))
      case D5(h: Old.S.typ<Old.S.typ<string>>) =>
        New.S.typ.D5(typOldToNew(h))
    }

    function mapBothDifferentOldToNew(m: Old.S.mapBothDifferent): New.S.mapBothDifferent
      decreases m
    {
      match m
      case D1(m: map<Old.S.foo, Old.S.option<string>>) =>
        New.S.mapBothDifferent.D1(mapMap(fooOldToNew, optionOldToNew, m))
      case D2(s: string) =>
        New.S.mapBothDifferent.D2(s)
    }

    function mapBothDifferentInOldToNew(m: Old.S.mapBothDifferentIn): New.S.mapBothDifferentIn
      decreases m
    {
      match m
      case D1(m: map<Old.S.foo, Old.S.option<Old.S._Companion.apBothDifferent.mapBothDifferent>>) =>
        New.S.mapBothDifferentIn.D1(mapMap(fooOldToNew, optionOldToNew, m))
      case D2(s: string) =>
        New.S.mapBothDifferentIn.D2(s)
    }

    function mapBuiltInOldToNew(m: Old.S.mapBuiltIn): New.S.mapBuiltIn
      decreases m
    {
      match m
      case E1(m: map<map<string, bool>, set<int>>) =>
        New.S.mapBuiltIn.E1(m)
      case E2(r: seq<real>, s: set<bool>) =>
        New.S.mapBuiltIn.E2(r, s)
    }
  }
