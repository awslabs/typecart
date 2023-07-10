// TODO Interesting example
// TODO The invariant here is supposedly that Pos/Neg(n) where n > 0
// TODO But this is not enforced by the code
// TODO So the code ends up being BC when it "should" not be

module SignedInt {

  datatype signed_int = Pos(nat) | Neg(nat) | Zero

  function int_to_signed_int (i: int): signed_int
  {
    if i > 0 then
      Pos(i as nat)
    else if i < 0 then
      Neg((-1 * i) as nat)
    else
      Zero
  }

  function signed_int_add (i: signed_int, j: signed_int): signed_int
  {
    match (i, j) {
      case (Pos(i), Pos(j)) => Pos (i + j)
      case (Pos(i), Neg(j)) => int_to_signed_int(i - j)
      case (Pos(i), Zero) => Pos(i)
      case (Neg(i), Pos(j)) => int_to_signed_int(j - i)
      case (Neg(i), Neg(j)) => int_to_signed_int(0 - i - j)
      case (Neg(i), Zero) => Neg(i)
      case (Zero, Zero) => Zero
      case (Zero, Pos(j)) => Pos(j)
      case (Zero, Neg(j)) => Neg(j)
    }
  }

  function add_signed_int (i: int, j: int): signed_int
  {
    signed_int_add (int_to_signed_int(i), int_to_signed_int(j))
  }

}
