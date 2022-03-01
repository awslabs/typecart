include "Old.dfy"
include "New.dfy"

  module Combine {

    import Old

    import New
    function method sigAOldToNew(s: Old.SignalA.sigA): New.SignalA.sigA
      decreases s
    {
      match s
      case IOSignal(msg: string) =>
        New.SignalA.sigA.IOSignal(msg)
      case Internal(msg: string) =>
        New.SignalA.sigA.Internal(msg)
    }

    function method sigBOldToNew(s: Old.SignalB.sigB): New.SignalB.sigB
      decreases s
    {
      match s
      case IOSignal(msg: string) =>
        New.SignalB.sigB.IOSignal(msg)
      case Internal(msg: string) =>
        New.SignalB.sigB.Internal(msg)
    }

    function method sigABOldToNew(s: Old.Eval.sigAB): New.Eval.sigAB
      decreases s
    {
      match s
      case SigA(aSig: Old.SignalA.sigA) =>
        New.Eval.sigAB.SigA(sigAOldToNew(aSig))
      case SigB(bSig: Old.SignalB.sigB) =>
        New.Eval.sigAB.SigB(sigBOldToNew(bSig))
    }

    function method resultOldToNew<U, U'>(fU: U -> U', r: Old.Eval.result<U>): New.Eval.result<U'>
      decreases r
    {
      match r
      case Failure(sig: Old.Eval.sigAB) =>
        New.Eval.result.Failure(sigABOldToNew(sig))
      case Success(value: U) =>
        New.Eval.result.Success(fU(value))
    }
  }
