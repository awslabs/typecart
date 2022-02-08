function seqMap<A, B>(f: A -> B, s: seq<A>) : (r:seq<B>)
  ensures |s| == |r|
{
  if s == [] then [] else [f(s[0])] + seqMap(f, s[1..])
}

predicate Injective<T(!new), U>(f: T --> U, s: set<T>)
  requires forall x: T :: x in s ==> f.requires(x)
{
  forall x, y :: x in s && y in s && x != y ==> f(x) != f(y)
}

function setMap<T, U>(f: T --> U, s: set<T>): (res: set<U>)
  requires forall x: T :: x in s ==> f.requires(x)
  ensures |res| <= |s|
  ensures Injective(f,s) ==> |s| == |res|
  ensures res == set x | x in s :: f(x)
{
  if s == {} then {}
  else
    var v :| v in s;
    {f(v)} + setMap(f,s - {v})
}

function mapMapKey<K, K', V>(f: K -> K', m: map<K, V>) : map<K', V>
{
  if m == map[] then map[]
  else
    var k :| k in m;
    var v := m[k];
    map[f(k) := v] + mapMapKey(f, m - {k})
}

function mapMapValue<K, V, V'>(f: V -> V', m: map<K, V>): (m':map<K, V'>)
  requires forall k:: k in m.Keys ==> f.requires(m[k])
  ensures m.Keys == m'.Keys
  ensures |m| == |m'|
{
  var result := map k | k in m :: f(m[k]);
  assert |result.Keys| == |result|;
  result
}

function mapMap<K, K', V, V'>(f: K -> K', g : V -> V', m: map<K, V>) : map<K', V'>
{
  if m == map[] then map[]
  else
    var k :| k in m;
    var v := m[k];
    map[f(k) := g(v)] + mapMap(f, g, m - {k})
}
