
  module Old.Old {
    module Old2 {
      import Old.Old1
      
      datatype nullableOption<T> = Null() | Original(o: option<T>) {
        
      }
      
      
      
    }
    
    
    module Old1 {
      datatype option<T> = None() | Some(val: T) {
        
      }
      
      
      
    }
    
    
    
  }
  
  
  module Old.New {
    module New1 {
      datatype option<T> = None() | Some(val: T) {
        
      }
      
      
      
    }
    
    
    
  }
  
  
  