module Old {
  datatype expr = Const(x: int) | Add(e1: expr, e2: expr) | Sub(e1: expr, e2: expr)
  datatype form<a> = Equal(x: a, y: a) | True | And(f1: form, f2: form)

  function simplify<a>(f: form<a>): form<a> {
    match f {
      case Equal(e1,e2) => Equal(e1,e2)
      case True => True
      case And(True,f2) => simplify(f2)
      case And(f1,True) => simplify(f1)
      case And(f1,f2) => And(simplify(f1), simplify(f2))
    }
  }
}

module New {
  datatype expr = Const(x: int) | Add(e1: expr, e2: expr) | Mul(e1: expr, e2: expr)
  datatype form<a> = Equal(x: a, y: a) | True | And(f1: form, f2: form)

  function simplify<a>(f: form<a>): form<a> {
    match f {
      case Equal(e1,e2) => Equal(e1,e2)
      case True => True
      case And(True,f2) => simplify(f2)
      case And(f1,True) => simplify(f1)
      case And(f1,f2) => And(simplify(f1), simplify(f2))
    }
  }
}

module FunctionalCompat {
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

  function formDefined<a>(a_defined: a -> bool, e: Old.form): bool {
    match e {
      case Equal(e1,e2) => a_defined(e1) && a_defined(e2)
      case And(f1, f2) => formDefined(a_defined,f1) && formDefined(a_defined,f2)
      case True => true
    }
  }

  function form<a_old,a_new>(a_defined: a_old -> bool, a: a_old -> a_new, f: Old.form<a_old>): New.form<a_new>
    requires formDefined(a_defined, f)
    {
      match f {
        case Equal(e1,e2) => New.Equal(a(e1),a(e2))
        case True => New.True
        case And(f1,f2) => New.And(form(a_defined, a, f1), form(a_defined, a, f2))
     }
    }


  lemma simplify<a_old,a_new>(a_defined: a_old -> bool, a: a_old -> a_new, f: Old.form<a_old>)
    requires formDefined(a_defined, f)
    ensures New.simplify(form(a_defined, a, f)) == form(a_defined, a, Old.simplify(f))
  {
    match f {
     case True =>
     case Equal(e1,e2) =>
     case And(f1,f2) => // verification fails here, not sure yet why
    }
  }
}

module RelationalCompat {
  import Old
  import New

  function expr(eO: Old.expr, eN: New.expr): bool
  {
    match (eO,eN) {
      case (Const(nO),Const(nN)) => nO == nN
      case (Add(e1O, e2O), Add(e1N,e2N)) => expr(e1O,e1N) && expr(e2O,e2N)
      case _ => false
    }
  }

  function form<a_old,a_new>(a: (a_old, a_new) -> bool, fO: Old.form<a_old>, fN: New.form<a_new>): bool
    {
      match (fO,fN) {
        case (Equal(e1O,e2O), Equal(e1N,e2N)) => a(e1O,e1N) && a(e2O,e2N)
        case (True,True) => true
        case (And(f1O,f2O), And(f1N,f2N)) => form(a, f1O, f1N) && form(a, f2O, f2N)
        case _ => false
     }
    }


  lemma simplify<a_old,a_new>(a: (a_old,a_new) -> bool, fO: Old.form<a_old>, fN: New.form<a_new>)
    requires form(a, fO, fN)
    ensures form(a, Old.simplify(fO), New.simplify(fN))
  {
    match (fO,fN) {
     case True =>
     case (Equal(e1O,e2O), Equal(e1N,e2N)) =>
       // a(e1O,e1N);
       // a(e2O,e2N);  // verification fails here, not sure yet why
     case (And(f1O,f2O), And(f1N,f2N)) =>
       // form(f1O,f1N)
       // form(f2O,f2N) // verification fails here, not sure yet why
    }
  }
}

