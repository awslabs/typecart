module List {

  datatype list<T> = Nil | Cons (T, list<T>)

  function length<T>(l: list<T>): int
  {
    match l {
      case Nil => 0
      case Cons (h, t) =>
        1 + length<T>(t)
    }
  }
}
