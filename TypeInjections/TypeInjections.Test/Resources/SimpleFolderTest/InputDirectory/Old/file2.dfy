
module S {

  datatype foo = Bar(x: int) | Baz(y: string)

  datatype seqOfBuiltin = B1(s: seq<int>, c: char) 
                        | B2(y: seq<seq<bool>>)
}