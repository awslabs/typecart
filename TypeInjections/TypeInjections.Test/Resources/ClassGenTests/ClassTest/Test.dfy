module Old {
  datatype foo = Bar | NotSoBar

  class AOk {
    var x: foo
    const y:int
    const z := 3
    constructor (x:foo, y:int) 
      ensures this.x == x
      ensures this.y == y
    {
      this.x := x;
      this.y := y;
    } 
  }

  class BNotOk {
    var x: foo
    var y: int
    constructor (x:foo) 
      ensures this.x == x
    {
      this.x := x;
    } 
  }

  class COk {
    var x: foo
    var y: int
    constructor (x:foo, y:int) 
      ensures this.x == x
      ensures this.y == y
    {
      this.x := x;
      this.y := y;
    } 
  }

  class CNotOk {
    var x: foo
    var y: int
    constructor (x:foo, y:int) 
      ensures this.x == x
    {
      this.x := x;
      this.y := y;
    } 
  }

  class DNotOk {
    var x: foo
    constructor (y:foo) 
      ensures this.x == y
    {
      this.x := y;
    } 
  }

  class GOk {
    var x: foo
    var y: int
    constructor (x:foo, y:int) 
      ensures this.y == y
      ensures this.x == x
    {
      this.x := x;
      this.y := y;
    } 
  }

  module tiny {
    datatype foo = Bar | NotSoBar
  }

  class EOk {
    var x: tiny.foo
    constructor (x:tiny.foo) 
      ensures this.x == x
    {
      this.x := x;
    } 
  }

  class INotOk {
    var x: foo
    var y: int
    constructor (x:foo, y:int) 
      ensures this.x == x
      ensures this.y == y
    {
      this.x := x;
      this.y := 2;
      this.y := y;
    } 
  }

  class JNotOk {
    var x: foo
    var y: int
    constructor (x:foo, y:int) 
      ensures this.x == x
      ensures this.y == 2
    {
      this.x := x;
      this.y := 2;
    } 
  }

  class LNotOk {
    var x: foo
    const y: int
    constructor (x:foo) 
      ensures this.x == x
      ensures this.y == 2
    {
      this.x := x;
      this.y := 2;
    } 
  }

  class TNotOk {
    var x: foo
    const y: int
    constructor (x:foo) 
      ensures this.x == x
    {
      this.x := x;
    } 
  }
}