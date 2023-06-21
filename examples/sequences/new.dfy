module Seq {
// Change int to real
function seqmap<A>(f: real-> A, s: seq<real>): seq<A>
{
  if s == [] then
    []
  else 
    [f(s[0])] + seqmap<A>(f, s[1..])
}

function reduce(f: (real, real) -> real, id: real, s: seq<real>): real
{
  if s == [] then
    id
  else 
    f(s[0], reduce(f, id, s[1..]))
}
}
