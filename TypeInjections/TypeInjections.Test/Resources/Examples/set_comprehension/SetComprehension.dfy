
module M {
    
   method blah() {
        var mapDisplay := map[1 := "a", 2 := "b"]; // map display expression
        var S := set x : nat, y : nat | x < 2 && y < 2 :: (x, y); // set comprehension
        var m1 := map x : int | 1 <= x <= 10 :: 2*x := 3*x; // more complicated instance of map comprehension
        var m2 := map x : int | 0 <= x <= 10 :: x * x; // map comprehension 
      }
}
