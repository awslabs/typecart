include "Old.dfy"
include "New.dfy"

  module Combine {

    import Old

    import New
    function method sigOldToNew(s: Old.SignalA.sig): New.SignalA.sig
      decreases s
    {
      match s
      case Recieve(value: string) =>
        New.SignalA.sig.Recieve(value)
      case Send(value: string) =>
        New.SignalA.sig.Send(value)
    }

    function method sigOldToNew(s: Old.SignalB.sig): New.SignalB.sig
      decreases s
    {
      match s
      case Recieve(value: string) =>
        New.SignalB.sig.Recieve(value)
      case Send(value: string) =>
        New.SignalB.sig.Send(value)
    }

    function method sigOldToNew(s: Old.Together.sig): New.Together.sig
      decreases s
    {
      match s
      case MsgA(aMsg: Old.SignalA.sig) =>
        New.Together.sig.MsgA(sigOldToNew(aMsg))
      case MsgB(bMsg: Old.SignalB.sig) =>
        New.Together.sig.MsgB(sigOldToNew(bMsg))
    }

    function method commOldToNew(c: Old.Together.comm): New.Together.comm
      decreases c
    {
      match c
      case Channel(value: Old.Together.sig) =>
        New.Together.comm.Channel(sigOldToNew(value))
    }
  }
