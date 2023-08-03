// unchanged
module Classes {
  class T {
    var x: int
    constructor (x: int) {
      this.x := x;
    }
    function getX(): int
      reads this
    {
      // dummy variables to ensure that we support "requires" here
      var es := [x];
      var _ := seq(|es|, i requires 0 <= i < |es| => es[i]);
      x
    }
  }

  class Wrapper<A> {
    var a: A
    constructor (a: A) {
      this.a := a;
    }
    method Amap<B>(f: A -> B) returns (m: Wrapper<B>) {
      m := new Wrapper(f(this.a));
    }
  }

  trait F<A,B> {
    function apply(a: A): B
  }
}
