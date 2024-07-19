module Translations.MapBuiltinTypes {
  function Seq<o,n>(t: o -> n, e: seq<o>) : (f : seq<n>)
    ensures |e| == |f|
    ensures forall i : int :: (0 <= i < |e| ==> f[i] == t(e[i]))
  {
    if e == [] then [] else [t(e[0])] + Seq(t, e[1..])
  }
  function Set<o,n>(t: o -> n, e: set<o>) : (f : set<n>)
    ensures forall x : o :: x in e ==> t(x) in f
    ensures forall x : n :: x in f ==> exists y : o :: y in e && t(y) == x
  {
    set x:o | x in e :: t(x)
  }
  /* We need a translation function from K_N to K_O in order to translate from map<K_O, V_O> to map<K_N, V_N>.
   * For example, if we want to translate sqr(x) = x * x from map<real, real> to map<int, int>
   * where K(x) = round(x), we need K2(x) = x * 1.0 so that sqr(1.4) = 1.96 is translated to
   * sqr(round(1.4)) = (round(1.4) * 1.0) * (round(1.4) * 1.0), i.e., sqr(1) = 1,
   * instead of sqr(round(1.4)) = round(1.4 * 1.4), i.e., sqr(1) = 2.
   */
  function Map<K_O,K_N(==),V_O,V_N(==)>(K: K_O -> K_N, K2: K_N -> K_O, V: V_O -> V_N, e: map<K_O, V_O>) : (f: map<K_N, V_N>)
  {
    var fKeys := set x: K_O | x in e.Keys && K2(K(x)) in e.Keys :: K(x);
    map a | a in fKeys :: V(e[K2(a)])
  }
}

module Translations.Utils {
  /* We requires false here because Dafny 4 does not allow non-determinism like ":|" in functions.
   * This function is to convert name resolution errors in stubs generated in translation functions
   * to verification errors (cannot prove false), so Dafny will not stop verifying the entire program
   * when it sees "???".
   */
  function ???<X(0)>(): X
    requires false
  {
    var tmp: X :| true;
    tmp
  }
}
