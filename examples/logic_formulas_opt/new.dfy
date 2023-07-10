module LogicFormulas {
  // change the implementation of eval()
  datatype formula = True | False | Not(formula) | And(formula, formula) | Or(formula, formula) | Implies(formula, formula)

  function eval(f: formula): bool
  {
    match f {
      case True => true
      case False => false
      case Not(g) => !(eval(g))
      case And(g, h) => eval(g) && eval(h)
      case Or(g, h) => eval(g) || eval(h)
      case Implies(g, h) => !eval(g) || eval(h)
    }
  }
}
