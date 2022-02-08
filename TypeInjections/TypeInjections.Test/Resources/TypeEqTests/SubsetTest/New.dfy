// We completely ignore the conditions for now
module Old.A {

  type string32Eq = s : string | 0 <= |s| <= 10

  // Can change names of generic parameters
  type map32Eq<X, Y> = m : map<X, Y> | 0 <= |m| < 5000

  // This wouldn't pass if we checked conditions
  type seq32Eq<T> = s : seq<T> | -1 <= |s| < 10

  // some more complicated ones
  predicate predOnMapsEq<K, V>(m: map<K, V>)

  type withFunEq<A, B> = m : map<A, B> | predOnMapsEq(m)

  type compoundEq<A, B> = m : map32Eq<A, B> | predOnMapsEq(m)

  datatype fooEq = Bar(x: int) | Baz(y: string)

  type withDatatypeEq = l: set<fooEq> | 0 <= |l| < 80

  // not equal
  type neq<T> = s : seq<T> | |s| == 3

  //generics are wrong
  type genNeq<K, V> = m: map<V, K> | |m| == 1
}
