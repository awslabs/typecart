module SignedInt {

  datatype signed_int = Pos(posnat) | Neg(posnat) | Zero
  newtype nonnegnat = n: nat | n >= 0
  newtype posnat = n: nat | n > 0 witness(1)

  function int_to_signed_int (i: int): signed_int
  {
    if i > 0 then
      Pos(i as posnat)
    else if i < 0 then
      Neg((-1 * i) as posnat)
    else
      Zero
  }

  function signed_int_add (i: signed_int, j: signed_int): signed_int
  {
    match (i, j) {
      case (Pos(i), Pos(j)) => Pos (i + j)
      case (Pos(i), Neg(j)) => int_to_signed_int(i as int - j as int)
      case (Pos(i), Zero) => Pos(i)
      case (Neg(i), Pos(j)) => int_to_signed_int(j as int - i as int)
      case (Neg(i), Neg(j)) => Neg(i + j)
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
