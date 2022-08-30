


  module Joint.ExprEval {
    datatype expr = Const(x: int) | Sub(e1: expr, e2: expr) {
      
    }
    
    
    function eval(e: expr):int
     {
      match e {
        case Const(mcc_0) => 
          var n:int:=mcc_0; n
        case Sub(mcc_1, mcc_2) => 
          var e2:expr:=mcc_2; var e1:expr:=mcc_1; (eval(e1) - eval(e2))
      }
      
    }
    
    
    
  }
  
  
  