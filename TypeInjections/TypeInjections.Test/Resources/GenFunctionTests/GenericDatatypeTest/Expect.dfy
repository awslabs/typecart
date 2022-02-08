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

    function listOldToNew<A, A'>(fA: A -> A', l: Old.Gen.list<A>): New.Gen.list<A'>
      decreases l
    {
      match l
      case Cons(x: A, tl: Old.Gen.list<A>) =>
        New.Gen.list.Cons(fA(x), listOldToNew(fA, tl))
      case Nil =>
        New.Gen.list.Nil
    }

    function treeOldToNew<A, A'>(fA: A -> A', t: Old.Gen.tree<A>): New.Gen.tree<A'>
      decreases t
    {
      match t
      case Left(l: Old.Gen.tree<A>) =>
        New.Gen.tree.Left(treeOldToNew(fA, l))
      case Node(a: A) =>
        New.Gen.tree.Node(fA(a))
      case Right(r: Old.Gen.tree<A>) =>
        New.Gen.tree.Right(treeOldToNew(fA, r))
    }

    function optionOldToNew<A, A'>(fA: A -> A', o: Old.Gen.option<A>): New.Gen.option<A'>
      decreases o
    {
      match o
      case None =>
        New.Gen.option.None
      case Some(x: A) =>
        New.Gen.option.Some(fA(x))
    }

    function eitherOldToNew<S, T, S', T'>(fS: S -> S', fT: T -> T', e: Old.Gen.either<S, T>): New.Gen.either<S', T'>
      decreases e
    {
      match e
      case Left(s: S) =>
        New.Gen.either.Left(fS(s))
      case Right(t: T) =>
        New.Gen.either.Right(fT(t))
    }

    function withSeqOldToNew<A, A'>(fA: A -> A', w: Old.Gen.withSeq<A>): New.Gen.withSeq<A'>
      decreases w
    {
      match w
      case Fst =>
        New.Gen.withSeq.Fst
      case Snd(l: seq<A>) =>
        New.Gen.withSeq.Snd(seqMap(fA, l))
    }

    function complicatedOldToNew<A, B, C, A', B', C'>(fA: A -> A', fB: B -> B', fC: C -> C', c: Old.Gen.complicated<A, B, C>): New.Gen.complicated<A', B', C'>
      decreases c
    {
      match c
      case C1(x: A, y: B, z: C) =>
        New.Gen.complicated.C1(fA(x), fB(y), fC(z))
      case C2(c: Old.Gen.complicated<B, A, C>) =>
        New.Gen.complicated.C2(complicatedOldToNew(fB, fA, fC, c))
      case C3(c2: Old.Gen.complicated<C, B, A>) =>
        New.Gen.complicated.C3(complicatedOldToNew(fC, fB, fA, c2))
    }

    function genRefOldToNew<A, B, A', B'>(fA: A -> A', fB: B -> B', g: Old.Gen.genRef<A, B>): New.Gen.genRef<A', B'>
      decreases g
    {
      match g
      case Left(l: Old.Gen.list<A>) =>
        New.Gen.genRef.Left(listOldToNew(fA, l))
      case Right(r: Old.Gen.tree<B>, z: Old.Gen.either<A, B>) =>
        New.Gen.genRef.Right(treeOldToNew(fB, r), eitherOldToNew(fA, fB, z))
    }
  }
