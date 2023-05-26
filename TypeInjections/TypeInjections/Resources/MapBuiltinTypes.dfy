module Translations.MapBuiltinTypes {
    export reveals Seq, Set, Map
    
    function Seq<o,n>(t: o -> n, e: seq<o>) : (f : seq<n>)
    ensures |e| == |f|
    ensures forall i : int :: (0 <= i < |e| ==> f[i] == t(e[i]))
    {
        if |e| == 0 then [] else
        seq(|e|, i => if 0 <= i < |e| then t(e[i]) else t(e[0]))
    }
    function Set<o,n>(t: o -> n, e: set<o>) : (f : set<n>)
    ensures forall x : o :: x in e ==> t(x) in f
    ensures forall x : n :: x in f ==> exists y : o :: y in e && t(y) == x
    {
        set x:o | x in e :: t(x)
    }
    function Map<K_O,K_N(==),V_O,V_N(==)>(K : K_O -> K_N, V : V_O -> V_N, e : map<K_O,V_O>) : (f: map<K_N,V_N>)   
    {
        var fKeys := set x: K_O | x in e.Keys :: K(x);
        var fSet := set x:K_O | x in e.Keys :: (K(x),V(e[x]));
        map a | a in fKeys :: var b :| (a,b) in fSet; b
    }
    /* Map helper functions and lemmas -- for proving map size meets standard of map31 */
    function fKeysFunc<T_O(!new), T_N>(T: T_O->T_N, m_O: set<T_O>) : set<T_N>
    {
        set x: T_O | x in m_O :: T(x)
    }
    function fSetFunc<T_O(!new), T_N(==), U_O, U_N>(T: T_O->T_N, U: U_O->U_N, m_O: map<T_O,U_O>) : (res : set<(T_N,U_N)>)
    {
        var fKeys := fKeysFunc(T,m_O.Keys);
        set x:T_O | x in m_O.Keys :: (T(x),U(m_O[x]))
    }
    function fMapFunc<T_O(!new), T_N(==), U_O, U_N(==)>(T: T_O->T_N, U: U_O->U_N, m_O: map<T_O,U_O>) : (res : map<T_N,U_N>)
    {
        var fKeys := fKeysFunc(T,m_O.Keys);
        var fSet := fSetFunc(T,U,m_O);
        map a | a in fKeys :: var b :| (a,b) in fSet; b 
    }
    lemma testfKeysSize<T_O(!new), T_N>(T: T_O->T_N, m_O: set<T_O>)
    requires forall x : T_O :: !exists y : T_O :: x != y && T(x) == T(y) 
    ensures |fKeysFunc(T,m_O)| == |m_O|
    {
        var fKeys := fKeysFunc(T,m_O);
        if |m_O| == 0 {
            assert |fKeysFunc(T,m_O)| == |m_O|;
        } else {
            var x :| x in m_O;
            var smallKeys := m_O - {x};
            var fSmallKeys := fKeysFunc(T,smallKeys);
            assert fKeys == fSmallKeys + {T(x)};
            assert |fKeys| == |fSmallKeys| + 1;
            testfKeysSize(T,smallKeys);
        }
    }
    lemma testMapSize<T_O(!new), T_N, U_O, U_N>(T: T_O->T_N, U: U_O->U_N, m_O: map<T_O,U_O>)
    requires forall x : T_O :: !exists y : T_O :: x != y && T(x) == T(y) 
    ensures |fMapFunc(T,U,m_O).Keys| == |m_O.Keys|;
    {
        var fKeys := fKeysFunc(T,m_O.Keys);
        testfKeysSize(T,m_O.Keys);
        assert |fKeys| == |m_O.Keys|;
        var fSet := fSetFunc(T,U,m_O);
        var fMap := map a | a in fKeys :: var b :| (a,b) in fSet; b ;
        if |m_O| == 0 {
            assert |fMap.Keys| == |m_O.Keys|;
        } else {
            var x :| x in fKeys;
            var smallKeys := fKeys - {x};
            var fMapSmall := map a | a in smallKeys :: var b :| (a,b) in fSet; b;
            assert fMap.Keys == fKeys;
            assert |fMap.Keys| == |fKeys|;
        }
    }
    function mapCreateGeneric<T_O(!new), T_N(==), U_O, U_N(==)>(T: T_O->T_N, U: U_O->U_N, m_O: map<T_O,U_O>) : (res : map<T_N,U_N>)
    requires forall x : T_O :: !exists y : T_O :: x != y && T(x) == T(y)
    ensures forall x :: x in m_O.Keys ==> T(x) in res.Keys
    ensures forall y :: y in m_O.Values ==> U(y) in res.Values
    ensures |m_O.Keys| == |res.Keys|
    {
        testfKeysSize(T,m_O.Keys);
        var fKeys := fKeysFunc(T,m_O.Keys);
        var fSet := fSetFunc(T,U,m_O);
        testMapSize(T,U,m_O);
        map a | a in fKeys :: var b :| (a,b) in fSet; b 
    }
    /* Set helper functions and lemmas -- for proving set size meets standard of set31 */
    function setCreate2Generic<o,n>(P : o -> n, S : set<o>) : set<n> 
    { set x: o | x in S :: P(x) }
    lemma setCreateSizeGeneric<o,n>(P : o -> n, S : set<o>)
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