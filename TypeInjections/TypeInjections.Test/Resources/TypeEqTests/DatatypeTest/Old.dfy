module Old.Test {

  datatype singleEq = A
  datatype singleNeq = B
  datatype singleArgEq = C(x : int)
  datatype singleArgNeq = D(x : int)
  datatype singleGenEq<A> = E(x: A)
  datatype singleGenNeq<A> = F(y: A)
  datatype singleSeqEq = G(z : seq<real>)
  datatype singleSeqNeq = H(a: seq<int>)
  datatype singlePrevEq = J(s : singleEq)
  // different type arguments
  datatype singlePrevNeq = K(s: singleArgEq)
  // syntactically matches but it relies on non-equal types
  datatype singlePrevWrongNeq = L(s: singleArgNeq)
  // not in other file
  datatype singleMissing = M(x: int)

  // multiple constructors
  datatype multiNeqArgsEq = A1 | A2
  datatype multiSimpleArgEq = C1 | C2(b: bool)
  datatype multiSimpleArgNeq = D1 | D2(b: bool)
  datatype multiSimpleArgsEq = E1(x: int) | E2(y: char)
  datatype multiSimpleArgsNeq = F1(x: bool) | F2(z: real)
  datatype multiCollArgsEq = G1(s: set<char>) | G2(i: seq<int>)
  datatype multiCollArgsNeq1 = H1(s: set<char>) | H2(i: seq<int>)
  datatype multiCollArgsNeq2 = I1(s: seq<int>) | I2(z: real)
  datatype multiGenArgEq<T> = J1(t: T) | J2(t: T)
  datatype multiGenArgNeq<T> = K1(t: T) | K2(x: int)
  datatype multiGenArgsEq<S, T> = L1(s: S) | L2(t: T)
  // the generic type params must be syntactically equal (at least for now)
  datatype multiGenArgsNeq<S, T> = M1(s: S) | M2(t: T)
  // list
  datatype listEq<T> = N1 | N2(x : T, m : listEq<T>)
  // binary tree
  datatype treeEq<T> = O1(x: T) | O2(t: treeEq<T>) | O3(t: treeEq<T>)
  // rose tree
  datatype roseTreeEq<T> = P1 (s: seq<roseTreeEq<T>>)

  // types that reference previously defined types
  datatype multiPrevSimpleEq = Q1(m: multiNeqArgsEq) | Q2(s: singleArgEq)
  // syntactically equal but references non-equal type
  datatype multiPrevSimpleNeq = R1(m: multiNeqArgsEq) | Q2(n:multiCollArgsNeq1)
  datatype multiPrevArgsEq = S1(x : multiGenArgEq<char>) | S2(y: multiGenArgEq<string>)
  datatype multiPrevArgsNeq = T1(x: multiGenArgEq<int>) | T2(y: multiGenArgEq<char>)
  datatype multiPrevArgsComplexEq = U1(x : multiGenArgsEq<int, seq<multiGenArgEq<int>>>) |
    U2(y : roseTreeEq<set<multiGenArgEq<seq<singleSeqEq>>>>)
  datatype multiPrevArgsComplexNeq1 = V1(x: multiGenArgsEq<int, seq<multiGenArgEq<int>>>) |
    V2(y : roseTreeEq<set<multiGenArgEq<seq<singleSeqEq>>>>)
  datatype multiPrevArgsComplexNeq2 = W1(x: multiGenArgsEq<int, seq<multiGenArgEq<int>>>) |
    W2(y : roseTreeEq<set<multiGenArgEq<seq<singleSeqEq>>>>)

  // tests with multiple type arguments in a single constructor
  datatype manyTypesEq = X1(x : int, y : char) | X2(s: string, l: seq<int>)
  datatype manyTypesNeq = Y1(x: int, y: char) | Y2(s: string, l: seq<int>)

  // tests for map
  datatype mapSimpleEq = Z1(m: map<int, string>) | Z2(n: set<char>)
  datatype mapSimpleKeyNeq = AA1(m: map<int, string>) | AA2
  datatype mapSimpleValueNeq = AB1 | AB2(m: map<int, string>)

  //tests for bit vectors
  datatype bitSimpleEq = AC1(b : bv32) | AC2
  datatype bitSimpleNeq = AD1 | AD2(b: bv32)

  //test for coinductive datatypes
  codatatype iListEq<T> = Nil | Cons(head : T, tail : iListEq<T>)
  codatatype streamEq<T> = More(head:T, tail: streamEq<T>)
  codatatype iTreeNeq<T> = Neqde(left : iTreeNeq<T>, value: T, right : iTreeNeq<T>)


}
