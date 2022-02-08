// Old.dfy and New.dfy have identical types
module New.A {
  datatype unaryNat = Z | S(n: unaryNat)

  datatype stringAlt = C(c: char) 
                     | A(hd: char, tl: stringAlt)

  datatype intTree =  Left(l: intTree) 
                   | Node (n: int) 
                   | Right (r: intTree)

  datatype complicated = A(x: complicated, y: complicated, z: int) 
                       | B(zero: complicated, r: string)
                       | C(u: char)
}
