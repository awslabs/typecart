module Translations.RelateBuiltinTypes {

    function Seq<o,n>(t: (o,n) -> bool, e: seq<o>, f: seq<n>) : (ret : bool)
    ensures (|e| == |f| && (forall i : int :: ((0 <= i < |f| && 0 <= i < |e|) ==> t(e[i],f[i]))))
        ==> ret == true
    {
        |e| == |f| && !(exists i : int :: 0 <= i < |e| && !t(e[i],f[i]))   
    }

    function Set<o,n>(t: (o,n) -> bool, e: set<o>, f: set<n>) : (ret : bool)
    {
        ((forall i : o :: i in e ==> exists j : n :: (j in f && t(i,j)))
        && (forall j : n :: j in f ==> exists i : o :: (i in e && t(i,j))))
    }

    function Map<K_O,K_N,V_O,V_N>(K : (K_O,K_N) -> bool, V : (V_O,V_N) -> bool, e : map<K_O,V_O>, f: map<K_N,V_N>) : (ret : bool)
    {
        (forall i : K_O :: i in e.Keys ==> (exists j : K_N :: j in f.Keys && K(i,j) && V(e[i],f[j])))
        && (forall i : K_O :: i in e.Keys ==> exists j : K_N :: j in f.Keys && K(i,j) && V(e[i],f[j]))
    }

    /*
    function Array<o,n>(t: (o,n) -> bool, e: array<o>, f: array<n>) : (ret : bool)
    reads e, f
    ensures (e.Length == f.Length && (forall i : int :: ((0 <= i < f.Length && 0 <= i < e.Length) ==> t(e[i],f[i]))))
         ==> ret == true
    {
        e.Length == f.Length && !(exists i : int :: 0 <= i < e.Length && !t(e[i],f[i]))   
    }
    */
}
