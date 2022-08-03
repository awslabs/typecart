
  module Combine.New {
    module New1 {
      function option<T_O, T_N>(T: (T_O,T_N)->bool, o_O: option<T_O>, o_N: option<T_N>):bool
       {
        match (o_O, o_N) {
          case (None(), None()) => 
            True
          case (Some(val_O), Some(val_N)) => 
            T(val_O, val_N)
          case _ => 
            False
        }
        
      }
      
      
      
    }
    
    
    
  }
  
  
  