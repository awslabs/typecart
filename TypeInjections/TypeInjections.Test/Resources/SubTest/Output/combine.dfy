
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
    
    
    
  }
  
  
  