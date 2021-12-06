include "Old.dfy"
include "New.dfy"

  module Combine {

    import Old

    import New
    function method fooOldToNew<A, A'>(fA: A -> A', f: Old.foo<A>): New.foo<A'>
      decreases f
    {
      match f
      case Bar(a: A) =>
        New.foo.Bar(fA(a))
      case NotSoBar =>
        New.foo.NotSoBar
    }

    function method AOkOldToNew<A(==), A'>(fA: A -> A', a: Old.AOk<A>): (a': New.AOk<A'>)
      ensures a'.x == fooOldToNew(fA, a.x)
      ensures a'.y == a.y
      decreases a

    method AOkOldToNewMethod<A(==), A'>(fA: A -> A', a: Old.AOk<A>) returns (a': New.AOk<A'>)
      ensures a'.x == AOkOldToNew(fA, a).x
      ensures a'.y == AOkOldToNew(fA, a).y
      decreases a
    {
      var temp: New.AOk<A'> := new New.AOk<A'>(fooOldToNew(fA, a.x), a.y);
      return temp;
    }

    function method BOkOldToNew<A(==), A'>(fA: A -> A', b: Old.BOk<A>): (b': New.BOk<A'>)
      ensures b'.x == AOkOldToNew(fA, b.x)
      decreases b

    method BOkOldToNewMethod<A(==), A'>(fA: A -> A', b: Old.BOk<A>) returns (b': New.BOk<A'>)
      ensures b'.x == BOkOldToNew(fA, b).x
      decreases b
    {
      var temp: New.BOk<A'> := new New.BOk<A'>(AOkOldToNew(fA, b.x));
      return temp;
    }
  }
