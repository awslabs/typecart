module Old {
  datatype foo<A> = Bar (a:A) | NotSoBar

  class AOk <A(==)>{
    var x: foo<A> 
    const y:int
    constructor (x:foo<A>, y:int) 
      ensures this.x == x
      ensures this.y == y
    {
      this.x := x;
      this.y := y;
    } 
  }

  class BOk<A(==)>{
    var x: AOk<A> 
    constructor (x:AOk<A>) 
      ensures this.x == x
    {
      this.x := x;
    } 
  }
}