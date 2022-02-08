// Old.dfy and New.dfy have identical types
module New.Gen {
  datatype list<A> = Nil 
                    | Cons(x: A, tl: list<A>)

  datatype tree<A> = Left(l: tree<A>) 
                   | Node(a: A) 
                   | Right(r: tree<A>)

  datatype option<A> = None 
                     | Some(x: A)

  datatype either<S, T> = Left(s: S) 
                        | Right (t: T)

  // cannot yet handle arbitrary seqs, but can handle with generics
  datatype withSeq<A> = Fst 
                      | Snd(l: seq<A>)

  datatype complicated<A, B, C> = C1(x: A, y: B, z: C) 
                                | C2(c: complicated<B, A, C>) 
                                | C3(c2: complicated<C, B, A>)

  datatype genRef<A, B> = Left(l: list<A>) 
                        | Right(r: tree<B>, z: either<A, B>)
}
