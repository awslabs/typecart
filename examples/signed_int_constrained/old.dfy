module SignedInt {

  datatype signed_int = Pos(nonnegnat) | Neg(posnat)
  newtype nonnegnat = n: nat | n >= 0
  newtype posnat = n: nat | n > 0 witness(1)

  function int_to_signed_int (i: int): (s: signed_int)
  {
    if i >= 0 then
      Pos(i as nonnegnat)
    else
      Neg((-1 * i) as posnat)
  }

  function signed_int_add (i: signed_int, j: signed_int): signed_int
  {
    match (i, j) {
      case (Pos(i), Pos(j)) => Pos (i + j)
      case (Pos(i), Neg(j)) => int_to_signed_int(i as int - j as int)
      case (Neg(i), Pos(j)) => int_to_signed_int(j as int - i as int)
      case (Neg(i), Neg(j)) => int_to_signed_int(0 - i as int - j as int)
    }
  }

  function add_signed_int (i: int, j: int): signed_int
  {
    signed_int_add (int_to_signed_int(i), int_to_signed_int(j))
  }

}
