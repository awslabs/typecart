module New.Lists {
  datatype Nat = Zero | Succ(n: Nat) {
      function plus(m: Nat): Nat {
          match m {
              case Zero => this
              case Succ(n) => Succ(this.plus(n))
          }
      }
  }

  datatype List<a> = Nil | Cons(h: a, t: List<a>) {
      function concat(l: List<a>): List<a> {
          match this {
              case Nil => l
              case Cons(h,t) => Cons(h, t.concat(l))
          }
      }
      function filter(f: a -> bool): List<a> {
          match this {
              case Nil => Nil
              case Cons(h,t) => if f(h) then Cons(h, t.filter(f)) else t.filter(f)
          }
      }
  }
}
