module IntType {
  newtype my_type = x: int | -0x80 <= x <= 0x7f
  function zero(): my_type
  {
    0
  }
  ghost function Zero(): my_type
  {
    0
  }
}

module RealType {
  newtype my_type = x: real | -128.0 <= x < 128.0
}

module Sqr {
  import opened IntType
  import opened RealType
  function squareInt(x: IntType.my_type): IntType.my_type
    requires -11 <= x <= 11
  {
    x * x
  }
  function squareReal(x: RealType.my_type): RealType.my_type
    requires x == 0.0
  {
    x * x
  }
}

module SqrInt {
  import opened IntType
  function square(x: my_type): my_type
    requires -11 <= x <= 11
  {
    x * x
  }
}
