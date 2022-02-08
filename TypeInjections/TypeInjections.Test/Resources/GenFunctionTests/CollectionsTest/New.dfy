// Old.dfy and New.dfy have identical types
module New.S {

  datatype foo = Bar(x: int) | Baz(y: string)

  datatype list<T> = Nil | Cons(h: T, tl: list<T>)

  //This test shows limitation of our tool
  // NOTE: the tool does not upport ex: set<list<foo>>
  datatype multipleColl = A1(s: seq<foo>, t: set<list<int>>) 
                        | A2(m: multipleColl) 
                        | A3(f: map<foo, string>, 
                             x: seq<set<map<int, char>>>, 
                             y: map<list<string>, list<set<set<int>>>>)
}
