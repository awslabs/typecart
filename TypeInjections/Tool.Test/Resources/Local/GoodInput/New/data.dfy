module ExprEval {

  datatype expr = Const(x: int) | Sub(e1: expr, e2: expr)

  function eval(e: expr): int {
    match e {
      case Const(n) => n
      case Sub(e1, e2) => eval(e1) - eval(e2)
    }
  }
}