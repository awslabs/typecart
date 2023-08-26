## Troubleshooting

Here are some common verification errors by Dafny and corresponding possible solutions.

#### Error: assertion might not hold

Dafny often cannot verify the proof sketch automatically. Example (`complex`):

```dafny
lemma mult_bc(x_O: Old.Complex.complex, y_O: Old.Complex.complex, x_N: New.Complex.complex, y_N: New.Complex.complex)
  requires x_N == complex_forward(x_O)
  requires y_N == complex_forward(y_O)
  ensures New.Complex.mult(x_N, y_N) == complex_forward(Old.Complex.mult(x_O, y_O))
{
  assert New.Complex.mult(x_N, y_N) == complex_forward((x_O.0 * y_O.0 - x_O.1 * y_O.1, x_O.0 * y_O.1 + x_O.1 * y_O.0));
}
```

In this specific case, an equivalent calc statement works:

```dafny
lemma mult_bc(x_O: Old.Complex.complex, y_O: Old.Complex.complex, x_N: New.Complex.complex, y_N: New.Complex.complex)
  requires x_N == complex_forward(x_O)
  requires y_N == complex_forward(y_O)
  ensures New.Complex.mult(x_N, y_N) == complex_forward(Old.Complex.mult(x_O, y_O))
{
  calc {
    New.Complex.mult(x_N, y_N);
      ==
    complex_forward((x_O.0 * y_O.0 - x_O.1 * y_O.1, x_O.0 * y_O.1 + x_O.1 * y_O.0));
  }
}
```

#### Error: cannot prove termination; try supplying a decreases clause

See "parent trick" at https://leino.science/papers/krml283.html.

#### Error: a precondition for this call could not be proved

For backward compatibility lemma calls generated in proof sketches, we can try commenting out the lemma call first to see
if Dafny can figure it out on its own. When Dafny cannot figure it out, it is recommended for the user to think how
to prove the precondition.
