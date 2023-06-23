module Complex {

  type complex = (int, int)

  function conjugate (x: complex): complex
  {
    (x.0, -1 * x.1)
  }

  function add(x: complex, y: complex): complex
  {
    (x.0 + y.0, x.1 + y.1)
  }

  function mult(x: complex, y: complex): complex
  {
    (x.0 * y.0 - x.1 * y.1, x.0 * y.1 + x.1 * y.0)
  }

  // this does not have to be implemented as a high order function
  // but it can be and I am doing so to understand how higher order behaves
  function normsquared (conjugate: complex -> complex, x: complex): int
  {
    mult(x, conjugate(x)).0
  }
}
