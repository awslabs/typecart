module ExprEval {
  // one constructor with more, one with fewer arguments
  datatype expr = Const(x: int) | Add(e1: expr, e2: expr, e3: expr) | Sub(e1: expr)

  function eval(e: expr): int {
    match e {
      case Const(n) => n
      case Add(e1,e2,e3) => eval(e1)+eval(e2)+eval(e3)
      case Sub(e) => -eval(e)
    }
  }

  lemma inversion(e1: expr, e2: expr)
    ensures eval(Add(e1, e2, Sub(e2))) == eval(e1)
  {}
}
