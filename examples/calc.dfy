module Old {
  datatype expr = Const(x: int) | Add(e1: expr, e2: expr) | Sub(e1: expr, e2: expr)

  function eval(e: expr): int {
    match e {
      case Const(n) => n
      case Add(e1, e2) => eval(e1) + eval(e2)
      case Sub(e1, e2) => eval(e1) - eval(e2)
    }
  }

  lemma addcorrect(e1: expr, e2: expr)
    ensures eval(Add(e1, e2)) == eval(Add(e2, e1))
  {}
}

module New {

  import Old

  datatype expr = Const(x: int) | Add(e1: expr, e2: expr) | Mul(e1: expr, e2: expr)

  function eval(e: expr): int {
    match e {
      case Const(n) => n
      case Add(e1, e2) => eval(e1) + eval(e2)
      case Mul(e1, e2) => eval(e1) * eval(e2)
    }
  }

  function hasSubtraction(e: Old.expr): bool {
    match e {
      case Sub(_, _) => true
      case Const(_) => false
      case Add(e1, e2) => hasSubtraction(e1) || hasSubtraction(e2)
    }
  }

  function tr(e: Old.expr): expr
    requires !hasSubtraction(e)
  {
    match e {
      case Const(n) => Const(n)
      case Add(e1, e2) => Add(tr(e1), tr(e2))
    }
  }

  lemma addcorrect(e1: expr, e2: expr)
    ensures eval(Add(e1, e2)) == eval(Add(e2, e1))
  {}
}


module Compat {
  import Old
  import New

  lemma compat(e: Old.expr)
    requires !New.hasSubtraction(e)
    ensures New.eval(New.tr(e)) == Old.eval(e)
  {}
}
