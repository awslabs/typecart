module ExprEval {
  datatype expr = Const(x: int) | Add(e1: expr, e2: expr) | Sub(e1: expr, e2: expr)

  function eval(e: expr): int {
    match e {
      case Const(n) => n
      case Add(e1, e2) => eval(e1) + eval(e2)
      case Sub(e1, e2) => eval(e1) - eval(e2)
    }
  }

  lemma inversion(e1: expr, e2: expr)
    ensures eval(Sub(Add(e1, e2),e2)) == eval(e1)
  {}
}
