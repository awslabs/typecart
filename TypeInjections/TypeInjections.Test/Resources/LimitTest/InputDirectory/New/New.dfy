// Old.dfy and New.dfy have identical types
// the tool generates idnetically named functions for types 
// with same names declared in separate modules
module MessageA {
  datatype msg = Send(value: string)
               | Recieve(value: string) {
    function method GetValue(): (ret: string)
      ensures ret == value
  }
}

module MessageB {
  datatype msg = Send(value: string)
               | Recieve(value: string) {
    function method GetValue(): (ret: string)
      ensures ret == value
  }
}

module Together{
  import MessageA
  import MessageB

  datatype msg = MsgA(aMsg: MessageA.msg) | MsgB(bMsg: MessageB.msg)

  datatype comm = Channel(value: msg) 
}
