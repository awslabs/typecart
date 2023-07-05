module Seq {
  // Change int to real. The user needs to add the following lemma in order to prove
  // the backward compatibility of seqmap:
  //   lemma bc_map<A_O, A_N>(A_forward: A_O->A_N, f:int -> A_O, s: seq<int>)
  //     ensures Translations.MapBuiltinTypes.Seq(A_forward, Old.Seq.seqmap(f, s)) == New.Seq.seqmap(((x1_N: real) => A_forward(f(x1_N.Floor))), Translations.MapBuiltinTypes.Seq(((sq_O: int) => sq_O as real), s))
  //   {}
  function seqmap<A>(f: real -> A, s: seq<real>): seq<A>
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
