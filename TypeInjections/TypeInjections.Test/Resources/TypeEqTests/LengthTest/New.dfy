// All of these types are not equivalent, but they should not throw any exceptions
module New.A {

  datatype lengthTypeArgsNeq<A, B> = A1(x: A) | A2(y: int)

  datatype lengthWithWithoutArgsNeq<A> = B1(x: int) | B2

  datatype lengthConstrutorsNeq = C1 | C2 | C3

  datatype lengthConstructorArgsNeq = D1(x: int) | D2(y: bool, z: seq<char>)
}
