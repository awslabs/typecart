module SignedInt {

  datatype signed_int = Pos(nat) | Neg(nat)

  function int_to_signed_int (i: int): signed_int
  {
    if i >= 0 then
      Pos(i as nat)
    else
      Neg((-1 * i) as nat)
  }

  function signed_int_add (i: signed_int, j: signed_int): signed_int
  {
    match (i, j) {
      case (Pos(i), Pos(j)) => Pos (i + j)
      case (Pos(i), Neg(j)) => int_to_signed_int(i - j)
      case (Neg(i), Pos(j)) => int_to_signed_int(j - i)
      case (Neg(i), Neg(j)) => int_to_signed_int(0 - i - j)
    }
  }

  function add_signed_int (i: int, j: int): signed_int
  {
    signed_int_add (int_to_signed_int(i), int_to_signed_int(j))
  }

}
