module Translations.MapBuiltinTypes {
    export reveals Seq, Set, Map
    
    function Seq<o,n>(t: o -> n, e: seq<o>) : (f : seq<n>)
    ensures |e| == |f|
    ensures forall i : int :: (0 <= i < |e| ==> f[i] == t(e[i]))
    {
        seq(|e|, i requires 0 <= i < |e| => t(e[i]))
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
    /* Set helper functions and lemmas -- for proving set size meets standard of set31 */
    function setCreate2Generic<o,n>(P: o -> n, S: set<o>) : set<n> 
    { set x: o | x in S :: P(x) }
    lemma setCreateSizeGeneric<o,n>(P: o -> n, S: set<o>)
    ensures |setCreate2Generic(P,S)| <= |S|
    {
        if |S| == 0 { 
        } else {
            var x: o :| x in S;
            assert setCreate2Generic(P,S) == setCreate2Generic(P,S - {x}) + {P(x)};
            setCreateSizeGeneric(P,S - {x});
        }
    }
}
