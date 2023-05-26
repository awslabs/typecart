// evalExpr is replaced with a different function evalExprAcc (different name, different header).
// The compatibility lemma for evalExpr cannot be generated
// The compatibility lemma for evalForm can still be generated and is still true,
// but the proof cannot use a generated lemma for evalExpr and is therefore harder.
// The user has to manually come up with the auxiliary lemma Old.evalExpr(e) = New.evalExprAcc(e,0).
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
      case Equal(e1,e2) => evalExprAcc(e1,0) == evalExprAcc(e2, 0)
      case And(f1,f2) => evalForm(f1) && evalForm(f2)
    }
  }
}
