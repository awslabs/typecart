
module S {



// BOOM NOW YOU SEE ME
  datatype foo = Bar(x: int) | Baz(y: string)

  datatype seqOfFoo = A1(s: seq<foo>) | A2

  datatype seqOfBuiltin = B1(s: seq<int>, c: char) 
                        | B2(y: seq<seq<bool>>)
}