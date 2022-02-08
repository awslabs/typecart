include "Old.dfy"
include "New.dfy"

  module Combine {

    import Old

    import New
    function singleNoArgsOldToNew(s: Old.A.singleNoArgs): New.A.singleNoArgs
      decreases s
    {
      match s
      case A1 =>
        New.A.singleNoArgs.A1
    }

    function twoNoArgsOldToNew(t: Old.A.twoNoArgs): New.A.twoNoArgs
      decreases t
    {
      match t
      case B1 =>
        New.A.twoNoArgs.B1
      case B2 =>
        New.A.twoNoArgs.B2
    }

    function manyNoArgsDiffOrderOldToNew(m: Old.A.manyNoArgsDiffOrder): New.A.manyNoArgsDiffOrder
      decreases m
    {
      match m
      case C1 =>
        New.A.manyNoArgsDiffOrder.C1
      case C2 =>
        New.A.manyNoArgsDiffOrder.C2
      case C3 =>
        New.A.manyNoArgsDiffOrder.C3
      case C4 =>
        New.A.manyNoArgsDiffOrder.C4
    }

    function singleArgOldToNew(s: Old.A.singleArg): New.A.singleArg
      decreases s
    {
      match s
      case D(x: int) =>
        New.A.singleArg.D(x)
    }

    function manyCtorsSingleArgOldToNew(m: Old.A.manyCtorsSingleArg): New.A.manyCtorsSingleArg
      decreases m
    {
      match m
      case E1(x: int) =>
        New.A.manyCtorsSingleArg.E1(x)
      case E2(y: char) =>
        New.A.manyCtorsSingleArg.E2(y)
      case E3(s: string) =>
        New.A.manyCtorsSingleArg.E3(s)
    }

    function singleCtorManyArgsOldToNew(s: Old.A.singleCtorManyArgs): New.A.singleCtorManyArgs
      decreases s
    {
      match s
      case F(b: bool, c: char, d: char) =>
        New.A.singleCtorManyArgs.F(b, c, d)
    }

    function manyCtorsManyArgsOldToNew(m: Old.A.manyCtorsManyArgs): New.A.manyCtorsManyArgs
      decreases m
    {
      match m
      case G1(x: int, y: int) =>
        New.A.manyCtorsManyArgs.G1(x, y)
      case G2(s: string, c: char, b: bool) =>
        New.A.manyCtorsManyArgs.G2(s, c, b)
      case G3(i: int, str: string) =>
        New.A.manyCtorsManyArgs.G3(i, str)
    }
  }
