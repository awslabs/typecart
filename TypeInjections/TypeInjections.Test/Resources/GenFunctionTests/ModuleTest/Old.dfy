// Old.dfy and New.dfy have identical types
// test for multiple modules
module Old.SignalA {
  datatype sigA = Internal(msg: string)
                | IOSignal(msg: string) {
    function method GetMessage(): (ret: string)
      ensures ret == msg
  }
}

module Old.SignalB {
  datatype sigB = Internal(msg: string)
                | IOSignal(msg: string) {
  function method GetMessage(): (ret: string)
      ensures ret == msg
  }
}

module Old.Eval{
  import SignalA
  import SignalB

  datatype sigAB = 
    SigA(aSig: SignalA.sigA) 
  | SigB(bSig: SignalB.sigB)

  datatype result<U> = 
    Success(value: U) 
  | Failure(sig: sigAB) 
}