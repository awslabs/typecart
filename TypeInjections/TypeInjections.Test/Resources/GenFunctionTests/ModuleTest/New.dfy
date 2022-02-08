// Old.dfy and New.dfy have identical types
// test for multiple modules
module New.SignalA {
  datatype sigA = Internal(msg: string)
                | IOSignal(msg: string) {
    function method GetMessage(): (ret: string)
      ensures ret == msg
  }
}

module New.SignalB {
  datatype sigB = Internal(msg: string)
                | IOSignal(msg: string) {
  function method GetMessage(): (ret: string)
      ensures ret == msg
  }
}

module New.Eval{
  import SignalA
  import SignalB

  datatype sigAB = 
    SigA(aSig: SignalA.sigA) 
  | SigB(bSig: SignalB.sigB)

  datatype result<U> = 
    Success(value: U) 
  | Failure(sig: sigAB) 
}