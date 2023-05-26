// Old.dfy and New.dfy have identical types 
module A {

  datatype singleNoArgs = A1

  datatype twoNoArgs = B2 | B1

  datatype manyNoArgsDiffOrder = C1 | C2 | C3 | C4

  datatype singleArg = D(x: int)

  // Add E3
  datatype manyCtorsSingleArg = E1(x: int) | E2(y: char) | E3(s: string)

  datatype singleCtorManyArgs = F(b: bool, c: char, d: char)

  // Add G3
  datatype manyCtorsManyArgs = G1(x: int, y: int) 
  							 | G2(s: string, c: char, b: bool) 
							   | G3 (i: int, str: string)

  function ident (x: manyCtorsManyArgs): manyCtorsManyArgs {
    x
  }
}
