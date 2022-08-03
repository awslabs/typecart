
include "file1_old.dfy"
include "file1_new.dfy"

  module Combine {

    import Old

    import New
    function method singleNoArgsOldToNew(s: Old.A.singleNoArgs): New.A.singleNoArgs
      decreases s
    {
      match s
      case A1 =>
        New.A.singleNoArgs.A1
    }


  }