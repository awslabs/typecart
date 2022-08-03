module FormEval {
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
