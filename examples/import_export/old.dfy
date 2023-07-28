module Option {
  export provides *
  export E provides a
  export F provides Option, Option.a
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
