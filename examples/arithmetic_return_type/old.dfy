module Arith {
  type Ident = string

  datatype Aexp =
    | CONST(n: int)
    | VAR(x: Ident)
    | PLUS(a1: Aexp, a2: Aexp)
    | MINUS(a1: Aexp, a2: Aexp)
    | MUL(a1: Aexp, a2: Aexp)

  predicate IdInAexp(id: Ident, a: Aexp) {
    match a
    case CONST(n) => false
    case VAR(id') => id == id'
    case PLUS(a1, a2) => IdInAexp(id,a1) || IdInAexp(id,a2)
    case MINUS(a1, a2) => IdInAexp(id,a1) || IdInAexp(id,a2)
    case MUL(a1, a2) => IdInAexp(id,a1) || IdInAexp(id, a2)
  }

  type Store = map<Ident,int>

  function Aeval(s: Store, a: Aexp): int
    requires forall id: Ident :: IdInAexp(id,a) ==> id in s
  {
    match a
    case CONST(n) => n
    case VAR(id) => s[id]
    case PLUS(a1, a2) => Aeval(s,a1) + Aeval(s,a2)
    case MINUS(a1, a2) => Aeval(s,a1) - Aeval(s,a2)
    case MUL(a1, a2) => Aeval(s,a1) * Aeval(s, a2)
  }
}
