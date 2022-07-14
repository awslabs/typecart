module Old {
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

module New {
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


module Compat {
  import Old
  import New

  // changes to members have no effect on the translation function
  function Nat(o: Old.Nat): New.Nat {
    match o {
      case Zero => New.Zero
      case Succ(n) => New.Succ(Nat(n))
    }
  }

  // homomorphism properties can be shown for the members shared by old and new version
  lemma Nat_plus(m: Old.Nat, n: Old.Nat)
    ensures Nat(m.plus(n)) == Nat(m).plus(Nat(n))
  {}

  // type parameters do not pose a fundamental problem for translation ...
  function List<a_old,a_new>(a: a_old -> a_new, l: Old.List<a_old>): New.List<a_new> {
      match l {
          case Nil => New.Nil
          case Cons(h,t) => New.Cons(a(h), List(a, t))
      }
  }

  lemma List_concat<a_old, a_new>(a: a_old -> a_new, l: Old.List<a_old>, m: Old.List<a_old>)
    ensures List(a, l.concat(m)) == List(a,l).concat(List(a,m))
  {}

  // but lemmas may fail when members use function arguments
  // In this special case, we can still construct a lemma that holds.
  // But it's unlikely we can generate, let alone auto-prove, such lemmas in general.
  lemma List_filter<a_old, a_new>(a: a_old -> a_new, l: Old.List<a_old>, f: a_old -> bool)
    requires forall x,y:a_old :: a(x) == a(y) ==> x == y
    ensures List(a, l.filter(f)) == List(a,l).filter(n => exists o:a_old :: a(o) == n && f(o))
  {
      // fails
  }

}
