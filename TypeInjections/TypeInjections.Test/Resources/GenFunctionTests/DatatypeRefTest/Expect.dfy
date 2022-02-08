include "Old.dfy"
include "New.dfy"

  module Combine {

    import Old

    import New
    function unaryNatOldToNew(u: Old.Ref.unaryNat): New.Ref.unaryNat
      decreases u
    {
      match u
      case S(n: Old.Ref.unaryNat) =>
        New.Ref.unaryNat.S(unaryNatOldToNew(n))
      case Z =>
        New.Ref.unaryNat.Z
    }

    function natRefOldToNew(n: Old.Ref.natRef): New.Ref.natRef
      decreases n
    {
      match n
      case A(y: Old.Ref.unaryNat) =>
        New.Ref.natRef.A(unaryNatOldToNew(y))
      case B(z: int) =>
        New.Ref.natRef.B(z)
    }

    function natRefRefOldToNew(n: Old.Ref.natRefRef): New.Ref.natRefRef
      decreases n
    {
      match n
      case Bar(u: Old.Ref.unaryNat) =>
        New.Ref.natRefRef.Bar(unaryNatOldToNew(u))
      case Foo(n1: Old.Ref.natRef, n2: Old.Ref.natRef) =>
        New.Ref.natRefRef.Foo(natRefOldToNew(n1), natRefOldToNew(n2))
    }

    function recAndRefOldToNew(r: Old.Ref.recAndRef): New.Ref.recAndRef
      decreases r
    {
      match r
      case A1(fst: Old.Ref.recAndRef, snd: Old.Ref.natRefRef) =>
        New.Ref.recAndRef.A1(recAndRefOldToNew(fst), natRefRefOldToNew(snd))
      case A2(x: Old.Ref.recAndRef, y: string, z: Old.Ref.recAndRef, aaa: Old.Ref.natRef) =>
        New.Ref.recAndRef.A2(recAndRefOldToNew(x), y, recAndRefOldToNew(z), natRefOldToNew(aaa))
      case A3 =>
        New.Ref.recAndRef.A3
    }
  }
