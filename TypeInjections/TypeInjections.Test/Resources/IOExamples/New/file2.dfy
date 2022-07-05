module New.ExprEval {
  datatype expr = Const(x: int) | Add(e1: expr, e2: expr) | Sub(e1: expr, e2: expr)

  function eval(e: expr): int {
    match e {
      case Const(n) => n
      case Add(e1, e2) => eval(e1) + eval(e2)
      case Sub(e1, e2) => eval(e1) - eval(e2)
    }
  }

  lemma commutative(e1: expr, e2: expr)
    ensures eval(Add(e1, e2)) == eval(Add(e2, e1))
  {}
}
