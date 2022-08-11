
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
  
  
  module Combine.Main {
    import Joint
    
    import Old
    
    import New
    
    import Util
    
    function T_FileTypes(F_O: Joint.Main.FileTypes, F_N: Joint.Main.FileTypes):bool
     {
      match (F_O, F_N) {
        case (Cfg(), Cfg()) => 
          /* unchanged constructor */ true
        case (Conf(), Conf()) => 
          /* unchanged constructor */ true
        case (Log(), Log()) => 
          /* unchanged constructor */ true
        case (Txt(), Txt()) => 
          /* unchanged constructor */ true
        case _ => 
          false
      }
      
    }
    
    
    lemma testAdd()
      ensures (Joint.Main.testAdd() == Joint.Main.testAdd())
    
    
    lemma testMul()
      ensures (Joint.Main.testMul() == Joint.Main.testMul())
    
    
    
  }
  
  
  