module Option {
  // change provides to reveals; should not affect anything
  export reveals *
  export E reveals a
  export F reveals Option, Option.a
  const a := 1
  datatype Option = A|B { static const a := 2 }
}

module X {
  import opened XYZ = Option
  method M() {
    print XYZ.a;
    print Option.a;
  }
}

module Y {
  // unsupported by typeCart now!
  import opened Option`E
  method M() {
    print Option.a;
  }
}

module Z {
  import opened Option`F
  method M() {
    print Option.a;
  }
}

method Main() {
  X.M();
  Y.M();
  Z.M();
}
