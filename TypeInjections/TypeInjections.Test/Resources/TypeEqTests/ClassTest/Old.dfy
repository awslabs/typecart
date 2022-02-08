module Old.A {

  class onlyFieldsEq {
    var g: bool
    var f: int

    constructor (g:bool, f:int) 
      ensures this.g == g
      ensures this.f == f
    {
      this.g := g;
      this.f := f;
    }
  }
  
  class ghostFieldsEq {
    var g: bool
    ghost var f: int

    constructor (g:bool, f:int) 
      ensures this.g == g
      ensures this.f == f
    {
      this.g := g;
      this.f := f;
    }
  }
  
  class ghostFieldsNeq {
    var g: bool
    ghost var f: int
    
    constructor (g:bool, f:int) 
      ensures this.g == g
      ensures this.f == f
    {
      this.g := g;
      this.f := f;
    }    
  }
  
  class onlyConstEq {
    const g: bool := true
    const f: int

    constructor (f:int) 
      ensures this.f == f
    {
      this.f := f;
    }
  }
  
  class onlyConstNeq {
    const g: bool := true
    const f: int

    constructor (f:int) 
      ensures this.f == f
    {
      this.f := f;
    }
  }

  class onlyConstExprNeq {
    const g: bool := true
  }
  
  class cEq<U(==)> {
    var g: bool
    var newMember: int8
    var f: int
    
    constructor (g:bool, newMember:int8, f:int) 
      ensures this.g == g
      ensures this.newMember == newMember
      ensures this.f == f
    {
      this.g := g;
      this.newMember := newMember;
      this.f := f;
    } 
  }
      
  class cTypeParamEq<U(==)> {
    var seqC: seq<U>
    
    constructor (seqC:seq<U>) 
      ensures this.seqC == seqC
    {
      this.seqC := seqC;
    } 
  }

  class cTypeParamsEq<U(==), V(==)> {
    var seqC: seq<U>
    var setC: set<V>

    constructor (seqC:seq<U>, setC:set<V>) 
      ensures this.seqC == seqC
      ensures this.setC == setC
    {
      this.seqC := seqC;
      this.setC := setC;
    } 
  }
  
  class cTypeParamsNeq<U(==), V(==)> {
    var seqC: seq<U>
    var setC: set<V>

    constructor (seqC:seq<U>, setC:set<V>) 
      ensures this.seqC == seqC
      ensures this.setC == setC
    {
      this.seqC := seqC;
      this.setC := setC;
    } 
  }
  
  class cNeq<U(==)> {
    var g: bool
    var newMember: int8
    var f: int
    var h: int

    constructor (g:bool, newMember:int8, f:int, h:int) 
      ensures this.g == g
      ensures this.newMember == newMember
      ensures this.f == f
      ensures this.h == h
    {
      this.g := g;
      this.newMember := newMember;
      this.f := f;
      this.h := h;
    } 
  }
  
  class xyEq {
    var x: xyEq?
  }

  class xEq {
    constructor() {
      x := null;
    }
    var x: xEq?
  }

  class xtraEq {
    constructor() {
      x := this.x;
    }
    var x: xtraEq?
  }

  ghost const INT_MAX := 0x7fff_ffff
  // byte/Byte
  newtype int8 = x | -128 <= x < 128
  // short/Short
  newtype int16 = x | -32768 <= x < 32768
}

module Old.B {
  module C {
    import opened A
    
    class eq {
      var g: bool
      var newMember: int8
      var another: set<int>
      var f: int

      constructor (g:bool, newMember:int8, another: set<int>, f:int) 
        ensures this.g == g
        ensures this.newMember == newMember
        ensures this.another == another
        ensures this.f == f
      {
        this.g := g;
        this.newMember := newMember;
        this.another := another;
        this.f := f;
      } 
    }
        
    class tEq {
      var g: bool
      var newMember: int8
      var another: T
      var f: int

      constructor (g:bool, newMember:int8, another: T, f:int) 
        ensures this.g == g
        ensures this.newMember == newMember
        ensures this.another == another
        ensures this.f == f
      {
        this.g := g;
        this.newMember := newMember;
        this.another := another;
        this.f := f;
      } 
    }
                
    class rEq {
      var g: bool
      var newMember: int8
      var another: extraEq
      var f: int

      constructor (g:bool, newMember:int8, another: extraEq, f:int) 
        ensures this.g == g
        ensures this.newMember == newMember
        ensures this.another == another
        ensures this.f == f
      {
        this.g := g;
        this.newMember := newMember;
        this.another := another;
        this.f := f;
      } 
    }
  
    class dEq<U(==),V(==)> {
      var g: bool
      var newMember: int8
      var another: set<U>
      var letsee: set<V>
      var f: int

      constructor (g:bool, newMember:int8, another: set<U>, letsee:set<V>, f:int) 
        ensures this.g == g
        ensures this.newMember == newMember
        ensures this.another == another
        ensures this.letsee == letsee
        ensures this.f == f
      {
        this.g := g;
        this.newMember := newMember; 
        this.another := another;
        this.letsee := letsee;
        this.f := f;
      } 
    }

    class dNeq<U(==),V(==)> {
      var g: bool
      var newMember: int8
      var another: set<U>
      var letsee: set<V>
      var f: int

      constructor (g:bool, newMember:int8, another: set<U>, letsee:set<V>, f:int) 
        ensures this.g == g
        ensures this.newMember == newMember
        ensures this.another == another
        ensures this.letsee == letsee
        ensures this.f == f
      {
        this.g := g;
        this.newMember := newMember; 
        this.another := another;
        this.letsee := letsee;
        this.f := f;
      } 
    }

    class jNeq<Q(==)> {
      var g: bool
      var newMember: int8
      var another: set<Q>
      var f: int
     
      constructor (g:bool, newMember:int8, another: set<Q>, f:int) 
        ensures this.g == g
        ensures this.newMember == newMember
        ensures this.another == another
        ensures this.f == f
      {
        this.g := g;
        this.newMember := newMember; 
        this.another := another;
        this.f := f;
      } 
    }

    ghost const Default := T.EMPTY

    datatype extraEq = NotSoExtra (i:int)

    datatype extraNeq = NotSoExtra (i:int)

    class aNeq {
      var x: extraNeq

      constructor (x:extraNeq) 
        ensures this.x == x
      {
        this.x := x;
      }
    }

    datatype T = T {
      static ghost const EMPTY: T
    }
  }
}
