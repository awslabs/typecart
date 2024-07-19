module Sign {
  function sign(i: int): (x: int) {
    if i == 0 then
      0
    else if i > 0 then
      1
    else
      -1
  } by method {
    if
    case i == 0 => x := 0;
    case i > 0 => x := 1;
    case i < 0 => x := -1;
  }
  method test(i: int) {
    var x := 0;
    if
    case i == 0 => x := 0;
    case i > 0 => x := 1;
    case i < 0 => x := -1;
  }
}
