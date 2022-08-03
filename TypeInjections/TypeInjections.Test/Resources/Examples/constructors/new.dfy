module ExprEval {
  // one added, one deleted constructor
  datatype expr = Const(x: int) | Add(e1: expr, e2: expr) | Mul(e1: expr, e2: expr)

  function eval(e: expr): int {
    match e {
      case Const(n) => n
      case Add(e1, e2) => eval(e1) + eval(e2)
      case Mul(e1, e2) => eval(e1) * eval(e2)
    }
  }

  lemma commutative(e1: expr, e2: expr)
    ensures eval(Add(e1, e2)) == eval(Add(e2, e1))
  {}
}
