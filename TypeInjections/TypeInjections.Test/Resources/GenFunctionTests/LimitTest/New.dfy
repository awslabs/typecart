// Old.dfy and New.dfy have identical types
// the tool generates idnetically named functions for types 
// with same names declared in separate modules
module New.SignalA {
  datatype sig = Send(value: string)
               | Recieve(value: string) {
    function method GetValue(): (ret: string)
      ensures ret == value
  }
}

module New.SignalB {
  datatype sig = Send(value: string)
               | Recieve(value: string) {
    function method GetValue(): (ret: string)
      ensures ret == value
  }
}

module New.Together{
  import SignalA
  import SignalB

  datatype sig = MsgA(aMsg: SignalA.sig) | MsgB(bMsg: SignalB.sig)

  datatype comm = Channel(value: sig) 
}
