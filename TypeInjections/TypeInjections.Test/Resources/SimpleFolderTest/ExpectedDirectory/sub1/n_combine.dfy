include "subFile1_old.dfy"
include "subFile1_new.dfy"

  module Combine.N {

    import Old

    import New
    function method fooOldToNew(f: Old.N.foo): (f': New.N.foo)
      ensures f as int == f' as int
      decreases f
    {
      f as int as New.N.foo
    }

    function method barOldToNew(b: Old.N.bar): (b': New.N.bar)
      ensures b as real == b' as real
      decreases b
    {
      b as real as New.N.bar
    }
  }