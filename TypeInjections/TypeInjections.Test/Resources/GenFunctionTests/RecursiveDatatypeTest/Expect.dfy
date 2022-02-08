include "Old.dfy"
include "New.dfy"

  module Combine {

    import Old

    import New
    function unaryNatOldToNew(u: Old.A.unaryNat): New.A.unaryNat
      decreases u
    {
      match u
      case S(n: Old.A.unaryNat) =>
        New.A.unaryNat.S(unaryNatOldToNew(n))
      case Z =>
        New.A.unaryNat.Z
    }

    function stringAltOldToNew(s: Old.A.stringAlt): New.A.stringAlt
      decreases s
    {
      match s
      case A(hd: char, tl: Old.A.stringAlt) =>
        New.A.stringAlt.A(hd, stringAltOldToNew(tl))
      case C(c: char) =>
        New.A.stringAlt.C(c)
    }

    function intTreeOldToNew(i: Old.A.intTree): New.A.intTree
      decreases i
    {
      match i
      case Left(l: Old.A.intTree) =>
        New.A.intTree.Left(intTreeOldToNew(l))
      case Node(n: int) =>
        New.A.intTree.Node(n)
      case Right(r: Old.A.intTree) =>
        New.A.intTree.Right(intTreeOldToNew(r))
    }

    function complicatedOldToNew(c: Old.A.complicated): New.A.complicated
      decreases c
    {
      match c
      case A(x: Old.A.complicated, y: Old.A.complicated, z: int) =>
        New.A.complicated.A(complicatedOldToNew(x), complicatedOldToNew(y), z)
      case B(zero: Old.A.complicated, r: string) =>
        New.A.complicated.B(complicatedOldToNew(zero), r)
      case C(u: char) =>
        New.A.complicated.C(u)
    }
  }
