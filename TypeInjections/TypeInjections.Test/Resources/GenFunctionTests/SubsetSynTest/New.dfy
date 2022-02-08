// Old.dfy and New.dfy have identical types
module New.N {
  
  module C {
    ghost const INT_MAX := 0x7fff_ffff
  }

  ghost const INT_MAX := 0x7fff_ffff

  type string32 = x: string | 0 <= |x| <= INT_MAX
  
  datatype Foo = Bar(x: int) | Baz(z: string)

  type map32<K, V> = m : map<K, V> | 0 <= |m| < INT_MAX

  // basic tests for subset types
  type FooSyn = Foo
  type FooSeq = s : seq<Foo> | 4 < |s| 
    witness [Bar (0), Bar (1), Bar (2), Bar (3), Bar (4)]

  type FooSet = s : set<Foo> | |s| < 4 

  // test for ChainingExpression
  type Map32Chain<K, V> = m : map<K, V> | |m| < 2 && INT_MAX == INT_MAX == INT_MAX 

  // TODO: does not verify
  // test for ExistsExpr
  const INT5 := 5
  type SeqExistsExpr = s : seq<int> | exists x :: 0 <= x <= INT5 && |s| == x
    witness [0, 1, 2, 3, 4]
  
  // test for ForallExpr
  type SeqForallExpr = s : seq<int> | forall x :: x in s ==> x == INT5
    witness [5]
  
  // test for ExprDotName
  type Map32ExprDotName<K, V> = m : map<K, V> | 0 <= |m| < C.INT_MAX
  
  // test for MemberSelectExpr and FunctionCallExpr
  predicate MapPred<K, V>(m: map<K, V>)
  {
    0 <= |m| < 10
  }
  type Context = m : map32<string32, Foo> | MapPred(m)

  // test for ApplyExpr
  type ContextApplyExpr = m : map32<string32, Foo> | (m => m) (MapPred(m))

  // test for BinaryExpr
  type ContextBinExpr = m : map32<string32, Foo> | MapPred(m) && MapPred(m)

  // test for ConversionExpr
  type C2 = i: int | 0 <= i
  const someC2 := 2
  type ConvMap = x: map32<string32, Foo>  | |x| <= someC2 as int

  // test for compound subset type
  type BoundedContext = c : Context | 0 <= |c| < 32

  // test for ITEExpr
  type SeqITE = s : seq<int> | 2 < |s| && s[1] == if s[0] == 2 then 2 else INT5
    witness [2, 2, 3] 

  // test for LambdaExpr
  type SeqLambda = s : seq<int> | |s| == 1 && ((n:int) => INT5) == ((n:int) => INT5)
    witness [0, 1]
  
  // test for LetExpr
  type SeqLetExpr = s : seq<int> | |s| == var x := INT5; var y := 1; x + y
    witness [0, 1, 2, 3, 4, 5] 
    
  datatype Outcome<T> = Success(value: T)
                      | Failure(error: string) {

    predicate method IsFailure() 
    { 
      this.Failure? 
    }
      
    function method PropagateFailure<U>(): Outcome<U>
      requires IsFailure() 
    {
      Failure(this.error) 
    }

    function method Extract(): T requires !IsFailure()
    {
      this.value 
    }
  }
  
  // test for LetOrFailExpr
  type SeqLetOrFailExpr = s : seq<int> 
    | |s| == var n := var x :- Success(INT5); Success(INT5); n.Extract()
    witness [0, 1, 2, 3, 4] 
    
  // test for MapComprehension
  type MapMapComprehension = x: map<int, int>  | x == map n: int | n == 0 :: INT5 * INT5 
    witness map [0 := 25] 

  // test for MapDisplayExpr
  type MapMapDisplayExpr = x: map<int, int>  | x == map[0 := 0, INT5 := INT5] 
    witness map[0 := 0, INT5 := INT5] 

    // test for MatchExpr
  datatype List<T> = Nil | Cons(head: T, tail: List<T>)

  type MapMatchExpr = x: map<int, int>  | 
    x == 
    match Cons(INT5, Nil)
      case Nil => map[0 := 0, INT5 := INT5]
      case Cons(_, _) => map[0 := 0, INT5 := INT5]
    witness map[0 := 0, INT5 := INT5] 

  // test for MultiSelectExpr
  const INT1 := 1
  type SetMultiSetDisplayExpr = s : multiset<int> | s == multiset {INT1,INT1}
    witness  multiset {INT1,INT1}
    
  // test for NestedMatchExpr
  type MapNestedMatchExpr = x: map<int, int>  | 
    x == 
    match Cons(INT5, Nil)
      case Nil => 
        (match Cons(INT5, Nil)
          case Nil => map[0 := 0, INT5 := INT5]
          case Cons(_, _) => map[0 := 0, INT5 := INT5])
      case Cons(_, _) => map[0 := 0, INT5 := INT5]
    witness map[0 := 0, INT5 := INT5] 
    
  // test for NegationExpression
  const NegInt1 := -1
  type SetNegationExpression = s : seq<int> | |s| == - NegInt1
    witness [0]
      
  // test for ParensExpression
  const Int1 := 1
  type SetParensExpression = s : seq<int> | |s| == (((Int1 + 0) - 0)+ 0)
    witness [0]

  // test for SeqConstructionExpr
  const Len := 1
  type SeqSeqConstructionExpr = s : seq<int> | s == seq<int>(Len,_ => Len)
    witness [1]
  
    // test for SeqDisplayExpr
  type SeqSeqDisplayExpr = x: seq<int> | x == [INT5, INT5] 
    witness [INT5, INT5] 
    
  // test for SeqSelectExpr
  type SeqSeqSelectExpr = x: seq<int> | |x| == 2 && x[Int1] == INT5 
    witness [INT5, INT5] 

  // test for SeqUpdateExpr
  type SeqSeqUpdateExpr = x: seq<int> | |x| == 2 && x[Int1 := INT5] == x 
    witness [INT5, INT5]
    
  // test for SetComprehension
  type SetSetComprehension = s: set<int> | |s| == 1 && s == set x:int | x == INT5
    witness {INT5}

  // test for SetDisplayExpr
  type SetSetDisplayExpr = x: set<int> | x == {INT5, Int1} 
    witness {INT5, Int1} 
    
  // test for StmtExpr
  type TypeStmtExpr = x: set<int> | assert true; x == {INT5, Int1} 
    witness {INT5, Int1} 
    
  // test for TypeTestExpr
  type TypeTypeTestExpr = x: bool | x == INT5 is int 
    witness true
  
}
