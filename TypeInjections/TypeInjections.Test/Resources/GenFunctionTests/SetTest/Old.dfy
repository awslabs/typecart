// Old.dfy and New.dfy have identical types
module Old.S {

  datatype foo = Bar(x: int) | Baz(y: string)

  datatype setOfFoo = A1(s: set<foo>) | A2

  datatype setOfBuiltin = B1(s: set<int>, c: char) 
                        | B2(y: set<set<bool>>)
}
