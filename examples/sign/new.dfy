module Sign {
  // change input type from int to real
  function sign(i: real): (x: int) {
    if i == 0.0 then
      0
    else if i > 0.0 then
      1
    else
      -1
  } by method {
    if
    case i == 0.0 => x := 0;
    case i > 0.0 => x := 1;
    case i < 0.0 => x := -1;
  }
  method test(i: real) {
    var x := 0;
    if
    case i == 0.0 => x := 0;
    case i > 0.0 => x := 1;
    case i < 0.0 => x := -1;
  }
}
