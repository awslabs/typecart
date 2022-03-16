module Old {
  datatype expr = Const(x: int) | Add(e1: expr, e2: expr) | Sub(e1: expr, e2: expr)
  datatype form = Equal(x: expr, y: expr) | And(f1: form, f2: form)

  function evalExpr(e: expr): int {
    match e {
      case Const(n) => n
      case Add(e1, e2) => evalExpr(e1) + evalExpr(e2)
      case Sub(e1, e2) => evalExpr(e1) - evalExpr(e2)
    }
  }

  function evalForm(f: form): bool {
    match f {
      case Equal(e1,e2) => evalExpr(e1) == evalExpr(e2)
      case And(f1,f2) => evalForm(f1) && evalForm(f2)
    }
  }
}

module New {
  // one deleted, one added constructor  
  datatype expr = Const(x: int) | Add(e1: expr, e2: expr) | Mul(e1: expr, e2: expr)
  datatype form = Equal(x: expr, y: expr) | And(f1: form, f2: form)

  function evalExpr(e: expr): int {
    match e {
      case Const(n) => n
      case Add(e1, e2) => evalExpr(e1) + evalExpr(e2)
      case Mul(e1, e2) => evalExpr(e1) * evalExpr(e2)
    }
  }

  function evalForm(f: form): bool {
    match f {
      case Equal(e1,e2) => evalExpr(e1) == evalExpr(e2)
      case And(f1,f2) => evalForm(f1) && evalForm(f2)
    }
  }
}


module Compat {
  import Old
  import New

  function exprDefined(e: Old.expr): bool {
    match e {
      case Const(_) => true
      case Add(e1, e2) => exprDefined(e1) && exprDefined(e2)
      case Sub(_, _) => false
    }
  }

  function expr(e: Old.expr): New.expr
    requires exprDefined(e)
  {
    match e {
      case Const(n) => New.Const(n)
      case Add(e1, e2) => New.Add(expr(e1), expr(e2))
    }
  }

  function formDefined(e: Old.form): bool {
    match e {
      case Equal(e1,e2) => exprDefined(e1) && exprDefined(e2)
      case And(f1, f2) => formDefined(f1) && formDefined(f2)
    }
  }

  function form(f: Old.form): New.form
    requires formDefined(f)
    {
      match f {
        case Equal(e1,e2) => New.Equal(expr(e1),expr(e2))
        case And(f1,f2) => New.And(form(f1), form(f2))
     }
    }

  // generated lemmas, dependencies between the function interfaces result in corresponding lemma calls in the proofs
  lemma evalExpr(e: Old.expr)
    requires exprDefined(e)
    ensures New.evalExpr(expr(e)) == Old.evalExpr(e)
  {}

  lemma evalForm(f: Old.form)
    requires formDefined(f)
    ensures New.evalForm(form(f)) == Old.evalForm(f)
  {
    match f {
     case Equal(e1,e2) =>
        evalExpr(e1);
        evalExpr(e2);
     case And(f1,f2) =>
    }
  }
}
