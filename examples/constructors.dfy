module Old {
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

module New {
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


module Compat {
  import Old
  import New

  
  // domain predicate for partial translation function, automatically generated
  function exprDefined(e: Old.expr): bool {
    match e {
      case Const(_) => true
      case Add(e1, e2) => exprDefined(e1) && exprDefined(e2)
      case Sub(_, _) => false
    }
  }

  // (partial) translation function for type of the same name
  function expr(e: Old.expr): New.expr
    requires exprDefined(e)
  {
    match e {
      case Const(n) => New.Const(n)
      case Add(e1, e2) => New.Add(expr(e1), expr(e2))
    }
  }

  // homomorphism property for function of the same name
  lemma eval(e: Old.expr)
    requires exprDefined(e)
    ensures New.eval(expr(e)) == Old.eval(e)
  {}
}
