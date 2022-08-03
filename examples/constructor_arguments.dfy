module Old {
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

module New {
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


module Compat {
  import Old
  import New

  
  // no way to generate a translation function
  // the system can only prdouce stubs/best guesses that the user has to adjust manually

  
  // in this case, the best guess happens to be the right predicate
  function exprDefined(e: Old.expr): bool {
    match e {
        case Const(n) => true
        case Add(e1,e2) => exprDefined(e1) && exprDefined(e2)
        case Sub(e1,e2) => exprDefined(e1) && exprDefined(e2)
    }
  }

  // code below shows both generated best guess and manual adjustment
  function expr(e: Old.expr): New.expr
    requires exprDefined(e)
  {
    match e {
      case Const(n) => New.Const(n)
      case Add(e1, e2) =>
         // New.Add(expr(e1), expr(e2), ???) // generated stub with gap for extra argument
         New.Add(expr(e1), expr(e2), New.Const(0))
      case Sub(e1,e2) =>
         // New.Sub(expr(e1)) // best guess that drops deleted argument, not correct, needs adjusting
         New.Add(expr(e1), New.Sub(expr(e2)), New.Const(0))
    }
  }

  // homomorphism property for function of the same name
  lemma eval(e: Old.expr)
    requires exprDefined(e)
    ensures New.eval(expr(e)) == Old.eval(e)
  {}
}
