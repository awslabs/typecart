module Arith {
  type Ident = string

  datatype Aexp =
    | CONST(n: int)
    | VAR(x: Ident)
    | PLUS(a1: Aexp, a2: Aexp)
    | MINUS(a1: Aexp, a2: Aexp)
    | MUL(a1: Aexp, a2: Aexp)
      // new constructor
    | DIV(a1: Aexp, a2: Aexp)

  predicate IdInAexp(id: Ident, a: Aexp) {
    match a
    case CONST(n) => false
    case VAR(id') => id == id'
    case PLUS(a1, a2) => IdInAexp(id,a1) || IdInAexp(id,a2)
    case MINUS(a1, a2) => IdInAexp(id,a1) || IdInAexp(id,a2)
    case MUL(a1, a2) => IdInAexp(id,a1) || IdInAexp(id, a2)
    // new case
    case DIV(a1, a2) => IdInAexp(id,a1) || IdInAexp(id, a2)
  }

  type Store = map<Ident,int>

  // add option type
  datatype Option<T> = None | Some(n: T)

  // change return type to option (not supported for now), add div case
  function Aeval(s: Store, a: Aexp): Option<int>
    requires forall id: Ident :: IdInAexp(id,a) ==> id in s
  {
    match a
    case CONST(n) => Some(n)
    case VAR(id) => Some(s[id])
    case PLUS(a1, a2) =>
      match (Aeval(s,a1), Aeval(s,a2)) {
        case (Some(n1), Some(n2)) => Some(n1 + n2)
        case _ => None
      }
    case MINUS(a1, a2) =>
      match (Aeval(s,a1), Aeval(s,a2)) {
        case (Some(n1), Some(n2)) => Some(n1 - n2)
        case _ => None
      }
    case MUL(a1, a2) =>
      match (Aeval(s,a1), Aeval(s,a2)) {
        case (Some(n1), Some(n2)) => Some(n1 * n2)
        case _ => None
      }
    case DIV(a1, a2) =>
      match (Aeval(s,a1), Aeval(s,a2)) {
        case (Some(n1), Some(n2)) => if n2 == 0 then None else Some(n1 / n2)
        case _ => None
      }
  }
}
