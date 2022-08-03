
  module Joint.N {
    newtype foo = x: int | (((0 <= x) && (x < 9)) || (x == 100))
    
    newtype bar = y: real | (((-9e-1 <= y) && (y <= 1e1)) && (y < 9e1))
    
    
  }
  
  
  