// Old.dfy and New.dfy have identical types
// test for multiple modules
module ExceptionA {
  datatype exnA = Runtime(msg: string)
                | IOException(msg: string) {
    function method GetMessage(): (ret: string)
      ensures ret == msg
  }
}

module ExceptionB {
  datatype exnB = Runtime(msg: string)
                | IOException(msg: string) {
  function method GetMessage(): (ret: string)
      ensures ret == msg
  }
}

module Eval{
  import ExceptionA
  import ExceptionB

  datatype exnAB = 
    ExnA(aExn: ExceptionA.exnA) 
  | ExnB(bExn: ExceptionB.exnB)

  datatype result<U> = 
    Success(value: U) 
  | Failure(exn: exnAB) 
}