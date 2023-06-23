module Complex {
  // change int to real
  type complex = (real, real)

  function conjugate (x: complex): complex
  {
    (x.0, -1.0 * x.1)
  }

  function add(x: complex, y: complex): complex
  {
    (x.0 + y.0, x.1 + y.1)
  }

  function mult(x: complex, y: complex): complex
  {
    (x.0 * y.0 - x.1 * y.1, x.0 * y.1 + x.1 * y.0)
  }

  function normsquared (conjugate: complex -> complex, x: complex): real
  {
    mult(x, conjugate(x)).0
  }
}
