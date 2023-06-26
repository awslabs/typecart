## Troubleshooting

Here are some common verification errors by Dafny and corresponding possible solutions.

#### `Error: a postcondition could not be proved on this return path`

Dafny sometimes cannot automatically reason about old/new function parameters. Example (`sequences`):

```dafny
lemma seqmap<A_O, A_N>(A_forward: A_O->A_N, A_backward: A_N->A_O, f_O: int->A_O, s_O: seq<int>, f_N: real->A_N, s_N: seq<real>)
  requires (f_N == ((x1_N: real) => A_forward(f_O(x1_N.Floor))))
  requires (s_N == Translations.MapBuiltinTypes.Seq(((sq_O: int) => sq_O as real), s_O))
  requires (forall x_O: A_O :: (A_backward(A_forward(x_O)) == x_O))
  ensures (Translations.MapBuiltinTypes.Seq(A_forward, Old.Seq.seqmap(f_O, s_O)) == New.Seq.seqmap(f_N, s_N))
{}
```

We need to manually remove the "new" parameters and replace them with translations of "old" parameters:

```dafny
lemma bc_map<A_O, A_N>(A_forward: A_O->A_N, f: int -> A_O, s: seq<int>)
  ensures Translations.MapBuiltinTypes.Seq(A_forward, Old.Seq.seqmap(f, s)) == New.Seq.seqmap(((x1_N: real) => A_forward(f(x1_N.Floor))), Translations.MapBuiltinTypes.Seq(((sq_O: int) => sq_O as real), s))
{}
```

then replace the empty body of `seqmap` with `{ bc_map(A_forward, f_O, s_O); }`.