
  module New.New {
    module New1 {
      datatype option<T> = None() | Some(val: T) {
        
      }
      
      
      
    }
    
    
    module New2 {
      import New.New1
      
      datatype nullableOption<T> = Null() | Original(o: option<T>) {
        
      }
      
      
      
    }
    
    
    
  }
  
  
  