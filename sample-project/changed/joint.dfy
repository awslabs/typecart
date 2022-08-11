
  module Joint.Util {
    export 
       provides sub, prod, sum
       reveals sub, prod, sum
    
    function sum(a: int, b: int):(res: int)
      ensures (res == (a + b))
     {
      (a + b)
    }
    
    
    function prod(a: int, b: int):(res: int)
      ensures (res == (a * b))
     {
      (a * b)
    }
    
    
    function sub(a: int, b: int):(res: int)
      ensures (res == (a - b))
     {
      (a - b)
    }
    
    
    
  }
  
  
  module Joint.Main {
    import Util
    
    datatype FileTypes = Cfg() | Conf() | Log() | Txt() {
      
    }
    
    
    function testAdd():(res: int)
      ensures (res == 5)
     {
      Util.sum(2, 3)
    }
    
    
    function testMul():(res: int)
      ensures (res == 20)
     {
      Util.prod(Util.prod(2, 5), 2)
    }
    
    
    
  }
  
  
  