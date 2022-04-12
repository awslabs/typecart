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


module FunctionalCompat {
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

// Alternative example using logical relations

// benefits
// * can handle higher-order function types
// * speculate, it may be able to handle classes (by using bisimulation)
// * can handle partial injection functions more easily because no extra exprDefined is needed
// * subsumes functional approach if we use a functional relation
// * can express more complex relations between old and new datatypes
// drawbacks
// * overkill if we have injection functions and relations get in the way
// * some proofs might be more involved
//   if relations are functional, some of the generated lemma preconditions are effectively "requires xN = ..."
//   these redundant lemma variables may (or many not) harm provers
    
module RelationalCompat {
  import Old
  import New

  // relation between old and new type (same name as the type)
  // RelationCompat.expr(eO,eN) iff FunctionalCompat.expr(eO) = eN
  function expr(eO: Old.expr, eN: New.expr): bool
  {
    match (eO,eN) {
      case (Const(nO),Const(nN)) => nO == nN
      case (Add(xO, yO), Add(xN,yN)) => expr(xO,xN) && expr(yO,yN)
      case _ => false
    }
  }

  // logical relation lemma property for function of the same name
  lemma eval(eO: Old.expr, eN: New.expr)
    requires expr(eO,eN)
    ensures Old.eval(eO) == New.eval(eN)
  {}
}
