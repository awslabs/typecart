module LogicFormulas {
  // "Implies" is removed.
  // There is a stub for "Implies" in the translation function.
  // We can prove the backward compatibility by writing "New.LogicFormulas.formula.Or(New.LogicFormulas.formula.Not(formula_forward(x5_O)), formula_forward(x6_O))" in the stub.
  datatype formula = True | False | Not(formula) | And(formula, formula) | Or(formula, formula)

  function eval(f: formula): bool
  {
    match f {
      case True => true
      case False => false
      case Not(g) => !(eval(g))
      case And(g, h) => eval(g) && eval(h)
      case Or(g, h) => eval(g) || eval(h)
    }
  }
}
