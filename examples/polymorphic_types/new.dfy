module Simplify {
  // add one case in the function simplify
  datatype expr = Const(x: int) | Add(e1: expr, e2: expr) | Sub(e1: expr, e2: expr)
  datatype form<a> = Equal(x: a, y: a) | True | And(f1: form, f2: form)

  function simplify<a>(f: form<a>): form<a> {
    match f {
      case Equal(e1,e2) => Equal(e1,e2)
      case True => True
      case And(True,True) => True
      case And(True,f2) => simplify(f2)
      case And(f1,True) => simplify(f1)
      case And(f1,f2) => And(simplify(f1), simplify(f2))
    }
  }
}
