
module New.N {

  newtype foo = x : int | 0 <= x < 9 || x == 100

  newtype bar = y : real | -0.9 <= y <= 10.0 && y < 90.0
}
