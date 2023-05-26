// Old.dfy and New.dfy have identical types
module A {

  datatype singleNoArgs = A1

  datatype twoNoArgs = B2 | B1

  datatype manyNoArgsDiffOrder = C4 | C1 | C3 | C2

  datatype singleArg = D(x: int)

  datatype manyCtorsSingleArg = E1(x: int) | E2(y: char)

  datatype singleCtorManyArgs = F(b: bool, c: char, d: char)

  datatype manyCtorsManyArgs = G1(x: int, y: int) 
  							 | G2(s: string, c: char, b: bool)

  function ident (x: manyCtorsManyArgs): manyCtorsManyArgs {
    G1(1,1)
  }
}
