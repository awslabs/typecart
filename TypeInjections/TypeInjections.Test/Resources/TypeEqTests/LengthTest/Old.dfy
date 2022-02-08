// All of these types are not equivalent, but they should not throw any exceptions
module Old.A {

  datatype lengthTypeArgsNeq<A> = A1(x: A) | A2(y: int)

  datatype lengthWithWithoutArgsNeq = B1(x: int) | B2

  datatype lengthConstrutorsNeq = C1 | C2

  datatype lengthConstructorArgsNeq = D1(x: int) | D2(y: bool)
}
