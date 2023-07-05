
module Util
{
  export provides sum, prod, sub

  function sum(a: int, b: int) : (res: int)
    ensures res == a + b
  {
    a + b
  }

  function prod(a: int, b: int) : (res: int)
    ensures res == a * b
  {
    a * b
  }

  function sub(a: int, b: int) : (res: int)
    ensures res == a - b
  {
    a - b
  }


}
