
  module Combine.S {
    function foo(f_O: foo, f_N: foo):bool
     {
      match (f_O, f_N) {
        case (Bar(x_O), Bar(x_N)) => 
          (x_O == x_N)
        case (Baz(y_O), Baz(y_N)) => 
          (y_O == y_N)
        case _ => 
          False
      }
      
    }
    
    
    function seqOfBuiltin(s_O: seqOfBuiltin, s_N: seqOfBuiltin):bool
     {
      match (s_O, s_N) {
        case (B1(s_O, c_O), B1(s_N, c_N)) => 
          (True && (c_O == c_N))
        case (B2(y_O), B2(y_N)) => 
          True
        case _ => 
          False
      }
      
    }
    
    
    
  }
  
  
  