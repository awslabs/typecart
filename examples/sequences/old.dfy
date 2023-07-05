module Seq {

  function seqmap<A>(f: int -> A, s: seq<int>): seq<A>
  {
    if s == [] then
      []
    else
      [f(s[0])] + seqmap<A>(f, s[1..])
  }

  function reduce(f: (int, int) -> int, id: int, s: seq<int>): int
  {
    if s == [] then
      id
    else
      f(s[0], reduce(f, id, s[1..]))
  }
}
