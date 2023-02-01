module FormEval {
  datatype expr = Const(x: int) | Add(e1: expr, e2: expr)
  datatype form = Equal(x: expr, y: expr) | And(f1: form, f2: form)

  function evalExprAcc(e: expr, acc: int): int {
    match e {
      case Const(n) => acc+n
      case Add(e1, e2) =>
         var e1V := evalExprAcc(e1, acc);
         evalExprAcc(e2, e1V)
    }
  }

  function evalForm(f: form): bool {
    match f {
      case Equal(e1,e2) => evalExprAcc(e1, 0) == evalExprAcc(e2, 0)
      case And(f1,f2) => evalForm(f1) && evalForm(f2)
    }
  }
}
