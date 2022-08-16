
  include "joint.dfy"
  
  include "old.dfy"
  
  include "new.dfy"
  
  module Combine.Util {
    import Joint
    
    import Old
    
    import New
    
    export 
       provides sub, prod, sum
       reveals sub, prod, sum
    
    lemma sum(a_O: int, b_O: int, a_N: int, b_N: int)
      requires (a_O == a_N)
      requires (b_O == b_N)
      ensures (Joint.Util.sum(a_O, b_O) == Joint.Util.sum(a_N, b_N))
    
    
    lemma prod(a_O: int, b_O: int, a_N: int, b_N: int)
      requires (a_O == a_N)
      requires (b_O == b_N)
      ensures (Joint.Util.prod(a_O, b_O) == Joint.Util.prod(a_N, b_N))
    
    
    lemma sub(a_O: int, b_O: int, a_N: int, b_N: int)
      requires (a_O == a_N)
      requires (b_O == b_N)
      ensures (Joint.Util.sub(a_O, b_O) == Joint.Util.sub(a_N, b_N))
    
    
    
  }
  
  
  