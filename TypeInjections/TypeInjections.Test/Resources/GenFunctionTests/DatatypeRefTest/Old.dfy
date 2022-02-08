// Old.dfy and New.dfy have identical types
// datatypes that reference others
module Old.Ref {
  datatype unaryNat = Z | S(n: unaryNat)

  datatype natRef = A(y: unaryNat) | B(z: int)

  datatype natRefRef = Foo(n1: natRef, n2: natRef) 
                     | Bar(u: unaryNat)

  datatype recAndRef = A1(fst : recAndRef, snd: natRefRef) 
                     | A2(x: recAndRef, y: string, z: recAndRef, aaa : natRef) 
                     | A3
}
