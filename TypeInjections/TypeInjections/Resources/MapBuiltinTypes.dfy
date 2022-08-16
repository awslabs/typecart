module Combine.MapBuiltinTypes {

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

    function Map<K_O,K_N,V_O,V_N>(K : K_O -> K_N, V : V_O -> V_N, e : map<K_O,V_O>) : (f: map<K_N,V_N>)
    //ensures |e.Keys| == |f.Keys|
    ensures forall x : K_N, y : V_N :: x in f.Keys && y in f.Values && f[x] == y 
        ==> (exists a : K_O, b : V_O :: a in e.Keys && e[a] == b && K(a) == x && V(b) == y)
    //ensures forall a : K_O, b : V_O :: a in e.Keys && b in e.Values && e[a] == b 
    //    ==> (exists x : K_N, y : V_N :: x in f.Keys && y in f.Values && f[x] == y && K(a) == x && V(b) == y)    
    {
        var fKeys := set x: K_O | x in e.Keys :: K(x);
        var fSet := set x:K_O | x in e.Keys :: (K(x),V(e[x]));
        map a | a in fKeys :: var b :| (a,b) in fSet; b
    }


}


