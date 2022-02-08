// Old.dfy and New.dfy have identical types
// the tool generates idnetically named functions for types 
// with same names declared in separate modules
module Old.SignalA {
  datatype sig = Send(value: string)
               | Recieve(value: string) {
    function method GetValue(): (ret: string)
      ensures ret == value
  }
}

module Old.SignalB {
  datatype sig = Send(value: string)
               | Recieve(value: string) {
    function method GetValue(): (ret: string)
      ensures ret == value
  }
}

module Old.Together{
  import SignalA
  import SignalB

  datatype sig = MsgA(aMsg: SignalA.sig) | MsgB(bMsg: SignalB.sig)

  datatype comm = Channel(value: sig) 
}