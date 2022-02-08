// Old.dfy and New.dfy have identical types
module Old.S {

  datatype foo = Bar(x: int) | Baz(y: string)

  datatype mapFooKey = A1(s: map<foo, int>) | A2

  datatype mapFooVal = B1(s: map<bool, foo>) | B2

  datatype mapFooBoth = C1(m: map<foo, foo>) | C3

  datatype option<T> = None | Some(x: T)

  datatype typ<T> = D0(st: option<T>)
                  | D1(s: option<string>)
                  | D2(f: typ<T>)
                  | D3(g: typ<string>)
                  // incorrect output
                  | D4(t: option<option<string>>)
                  // incorrect output
                  | D5(h: typ<typ<string>>)
  
  // doesn't map correctly
  datatype mapBothDifferent = D1(m: map<foo, option<string>>) 
                            | D2(s: string)
  
  // doesn't map correctly
  datatype mapBothDifferentIn = D1(m: map<foo, option<mapBothDifferent>>) 
                              | D2(s: string)

  datatype mapBuiltIn = E1(m: map<map<string, bool>, set<int>>) 
                      | E2 (r: seq<real>, s: set<bool>)
}
