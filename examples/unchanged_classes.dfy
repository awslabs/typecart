module Old {
  class T {
      var x: int
      constructor (x: int) {
          this.x := x;
      }
      function getX(): int {x}
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

module Compat {
  import Old
  // we only consider the trivial case where there are no changes
  import New = Old

  // even for an unchanged class, we can have an injection function only if the class has
  // - methods to retrieve its current state
  // - a constructor to create a new instance from such a state
  // (which in particular excludes all traits)
  // In that case, one might as well use a datatype instead of a class.
  method T(o: Old.T) returns (n: New.T) {
      n := new New.T(o.getX());
  }

  // classes with map methods are an important exception. This incldues monads.
  method Wrapper<A_old,A_new>(A: A_old -> A_new, a: Old.Wrapper<A_old>) returns (n: New.Wrapper<A_new>) {
      n := a.Amap(A);
  }

  // In general, traits with type parameters allow simulating higher-order functions, to which functional homomorphisms cannot be extended 
  // So we cannot expect translation functions for any trait.
  // Similar problems arise for any trait with a method that uses a type parameter in negative position.
  function F<A_old,A_new,B_old,B_new>(A: A_old -> A_new, B: B_old -> B_old, f: F<A_old,B_old>): New.F<A_new,B_new> {
      // A_old --- A ---> A_new
      //  |                |
      //  f.apply         F(f).apply not definable
      //  |                |
      //  V                V
      // B_old --- B ---> B_new
      null
  }
}

