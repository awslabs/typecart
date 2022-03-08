include "Old.dfy"
include "New.dfy"

  module Combine {

    import Old

    import New
    function method mapMapValue<K, V, V'>(f: V -> V', m: map<K, V>): (m': map<K, V'>)
      requires forall k: K :: k in m.Keys ==> f.requires(m[k])
      ensures m.Keys == m'.Keys
      ensures |m| == |m'|
      decreases m
    {
      var result: map<K, V'> := map k: K {:trigger m[k]} {:trigger k in m} | k in m :: f(m[k]);
      assert |result.Keys| == |result|;
      result
    }

    function method setMap<T, U>(f: T --> U, s: set<T>): (res: set<U>)
      requires forall x: T :: x in s ==> f.requires(x)
      ensures |res| <= |s|
      ensures Injective(f, s) ==> |s| == |res|
      ensures res == set x: T {:trigger f(x)} {:trigger x in s} | x in s :: f(x)
      decreases s
    {
      if s == {} then
        {}
      else
        var v: T :| v in s; {f(v)} + setMap(f, s - {v})
    }

    function method seqMap<A, B>(f: A -> B, s: seq<A>): (r: seq<B>)
      ensures |s| == |r|
      decreases s
    {
      if s == [] then
        []
      else
        [f(s[0])] + seqMap(f, s[1..])
    }

    function method mapMap<K, K', V, V'>(f: K -> K', g: V -> V', m: map<K, V>): map<K', V'>
      decreases m
    {
      if m == map[] then
        map[]
      else
        var k: K :| k in m; var v: V := m[k]; map[f(k) := g(v)] + mapMap(f, g, m - {k})
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

    function string32OldToNew(s: Old.N.string32): New.N.string32
      requires 0 <= |s| && |s| <= New.N.INT_MAX
      decreases s
    {
      s
    }

    function method FooOldToNew(f: Old.N.Foo): New.N.Foo
      decreases f
    {
      match f
      case Bar(x: int) =>
        New.N.Foo.Bar(x)
      case Baz(z: string) =>
        New.N.Foo.Baz(z)
    }

    function map32OldToNew<K, V, K', V'>(fK: K -> K', fV: V -> V', m: Old.N.map32<K, V>): New.N.map32<K', V'>
      requires 0 <= |mapMap(fK, fV, m)| && |mapMap(fK, fV, m)| < New.N.INT_MAX
      decreases m
    {
      mapMap(fK, fV, m)
    }

    function FooSynOldToNew(f: Old.N.FooSyn): New.N.FooSyn
      decreases f
    {
      FooOldToNew(f)
    }

    function FooSeqOldToNew(f: Old.N.FooSeq): New.N.FooSeq
      requires 4 < |seqMap(FooOldToNew, f)|
      decreases f
    {
      seqMap(FooOldToNew, f)
    }

    function FooSetOldToNew(f: Old.N.FooSet): New.N.FooSet
      requires |setMap(FooOldToNew, f)| < 4
      decreases f
    {
      setMap(FooOldToNew, f)
    }

    function SeqExistsExprOldToNew(s: Old.N.SeqExistsExpr): New.N.SeqExistsExpr
      requires exists x: int :: 0 <= x && x <= New.N.INT5 && |s| == x
      decreases s
    {
      s
    }

    function SeqForallExprOldToNew(s: Old.N.SeqForallExpr): New.N.SeqForallExpr
      requires forall x: int :: x in s ==> x == New.N.INT5
      decreases s
    {
      s
    }

    function Map32ExprDotNameOldToNew<K, V, K', V'>(fK: K -> K', fV: V -> V', m: Old.N.Map32ExprDotName<K, V>): New.N.Map32ExprDotName<K', V'>
      requires 0 <= |mapMap(fK, fV, m)| && |mapMap(fK, fV, m)| < New.N.C.INT_MAX
      decreases m
    {
      mapMap(fK, fV, m)
    }

    function ContextOldToNew(c: Old.N.Context): New.N.Context
      requires New.N.MapPred(mapMapValue(FooOldToNew, c))
      decreases c
    {
      mapMapValue(FooOldToNew, c)
    }

    function ContextApplyExprOldToNew(c: Old.N.ContextApplyExpr): New.N.ContextApplyExpr
      requires ((m: bool) => m)(New.N.MapPred(mapMapValue(FooOldToNew, c)))
      decreases c
    {
      mapMapValue(FooOldToNew, c)
    }

    function ContextBinExprOldToNew(c: Old.N.ContextBinExpr): New.N.ContextBinExpr
      requires New.N.MapPred(mapMapValue(FooOldToNew, c)) && New.N.MapPred(mapMapValue(FooOldToNew, c))
      decreases c
    {
      mapMapValue(FooOldToNew, c)
    }

    function C2OldToNew(c: Old.N.C2): New.N.C2
      requires 0 <= c
      decreases c
    {
      c
    }

    function ConvMapOldToNew(c: Old.N.ConvMap): New.N.ConvMap
      requires |mapMapValue(FooOldToNew, c)| <= New.N.someC2 as int
      decreases c
    {
      mapMapValue(FooOldToNew, c)
    }

    function BoundedContextOldToNew(b: Old.N.BoundedContext): New.N.BoundedContext
      requires 0 <= |mapMapValue(FooOldToNew, b)| && |mapMapValue(FooOldToNew, b)| < 32
      decreases b
    {
      mapMapValue(FooOldToNew, b)
    }

    function SeqITEOldToNew(s: Old.N.SeqITE): New.N.SeqITE
      requires 2 < |s| && s[1] == if s[0] == 2 then 2 else New.N.INT5
      decreases s
    {
      s
    }

    function SeqLambdaOldToNew(s: Old.N.SeqLambda): New.N.SeqLambda
      requires |s| == 1 && ((n: int) => New.N.INT5) == (n: int) => New.N.INT5
      decreases s
    {
      s
    }

    function SeqLetExprOldToNew(s: Old.N.SeqLetExpr): New.N.SeqLetExpr
      requires |s| == var x: int := New.N.INT5; var y: int := 1; x + y
      decreases s
    {
      s
    }

    function method OutcomeOldToNew<T, T'>(fT: T -> T', o: Old.N.Outcome<T>): New.N.Outcome<T'>
      decreases o
    {
      match o
      case Failure(error: string) =>
        New.N.Outcome.Failure(error)
      case Success(value: T) =>
        New.N.Outcome.Success(fT(value))
    }

    function SeqLetOrFailExprOldToNew(s: Old.N.SeqLetOrFailExpr): New.N.SeqLetOrFailExpr
      requires |s| == var n: Outcome<int> := var valueOrError0: Outcome<int> := New.N.Outcome.Success(New.N.INT5); if valueOrError0.New.N.Outcome.IsFailure() then valueOrError0.New.N.Outcome.PropagateFailure() else var x: int := valueOrError0.New.N.Outcome.Extract(); New.N.Outcome.Success(New.N.INT5); n.New.N.Outcome.Extract()
      decreases s
    {
      s
    }

    function MapMapComprehensionOldToNew(m: Old.N.MapMapComprehension): New.N.MapMapComprehension
      requires m == map n: int | n == 0 :: New.N.INT5 * New.N.INT5
      decreases m
    {
      m
    }

    function MapMapDisplayExprOldToNew(m: Old.N.MapMapDisplayExpr): New.N.MapMapDisplayExpr
      requires m == map[0 := 0, New.N.INT5 := New.N.INT5]
      decreases m
    {
      m
    }

    function method ListOldToNew<T, T'>(fT: T -> T', l: Old.N.List<T>): New.N.List<T'>
      decreases l
    {
      match l
      case Cons(head: T, tail: Old.N.List<T>) =>
        New.N.List.Cons(fT(head), ListOldToNew(fT, tail))
      case Nil =>
        New.N.List.Nil
    }

    function MapMatchExprOldToNew(m: Old.N.MapMatchExpr): New.N.MapMatchExpr
      requires m == match New.N.List.Cons(New.N.INT5, New.N.List.Nil) { case Nil => map[0 := 0, New.N.INT5 := New.N.INT5] case Cons(_mcc#0: int, _mcc#1: List<int>) => map[0 := 0, New.N.INT5 := New.N.INT5] }
      decreases m
    {
      m
    }

    function MapNestedMatchExprOldToNew(m: Old.N.MapNestedMatchExpr): New.N.MapNestedMatchExpr
      requires m == match New.N.List.Cons(New.N.INT5, New.N.List.Nil) { case Nil => match New.N.List.Cons(New.N.INT5, New.N.List.Nil) { case Nil => map[0 := 0, New.N.INT5 := New.N.INT5] case Cons(_mcc#4: int, _mcc#5: List<int>) => map[0 := 0, New.N.INT5 := New.N.INT5] } case Cons(_mcc#2: int, _mcc#3: List<int>) => map[0 := 0, New.N.INT5 := New.N.INT5] }
      decreases m
    {
      m
    }

    function SetNegationExpressionOldToNew(s: Old.N.SetNegationExpression): New.N.SetNegationExpression
      requires |s| == 0 - New.N.NegInt1
      decreases s
    {
      s
    }

    function SetParensExpressionOldToNew(s: Old.N.SetParensExpression): New.N.SetParensExpression
      requires |s| == New.N.Int1 + 0 - 0 + 0
      decreases s
    {
      s
    }

    function SeqSeqConstructionExprOldToNew(s: Old.N.SeqSeqConstructionExpr): New.N.SeqSeqConstructionExpr
      requires s == seq<int>(New.N.Len, (_: int) => New.N.Len)
      decreases s
    {
      s
    }

    function SeqSeqDisplayExprOldToNew(s: Old.N.SeqSeqDisplayExpr): New.N.SeqSeqDisplayExpr
      requires s == [New.N.INT5, New.N.INT5]
      decreases s
    {
      s
    }

    function SeqSeqSelectExprOldToNew(s: Old.N.SeqSeqSelectExpr): New.N.SeqSeqSelectExpr
      requires |s| == 2 && s[New.N.Int1] == New.N.INT5
      decreases s
    {
      s
    }

    function SeqSeqUpdateExprOldToNew(s: Old.N.SeqSeqUpdateExpr): New.N.SeqSeqUpdateExpr
      requires |s| == 2 && s[New.N.Int1 := New.N.INT5] == s
      decreases s
    {
      s
    }

    function SetSetComprehensionOldToNew(s: Old.N.SetSetComprehension): New.N.SetSetComprehension
      requires |s| == 1 && s == set x: int | x == New.N.INT5 :: x
      decreases s
    {
      s
    }

    function SetSetDisplayExprOldToNew(s: Old.N.SetSetDisplayExpr): New.N.SetSetDisplayExpr
      requires s == {New.N.INT5, New.N.Int1}
      decreases s
    {
      s
    }

    function TypeStmtExprOldToNew(t: Old.N.TypeStmtExpr): New.N.TypeStmtExpr
      requires assert true; t == {New.N.INT5, New.N.Int1}
      decreases t
    {
      t
    }

    function TypeTypeTestExprOldToNew(t: Old.N.TypeTypeTestExpr): New.N.TypeTypeTestExpr
      requires t == New.N.INT5 is int
      decreases t
    {
      t
    }
  }
