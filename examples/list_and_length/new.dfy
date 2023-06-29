module List {
  // The new list is intended to store the length of each sublist in the data structure.
  // The forward function cannot ensure this, but we can have a separate requirement for this.

  datatype list<T> = Nil | Cons (T, list<T>, int)

  // Check that a list is correctly "lengthed"
  // And return the length
  function check_list<T>(ll:list<T>): (bool, int)
  {
    match ll {
      case Nil => (true, 0)
      case Cons(h, t, len) =>
        var (is_good_t, len_t):= check_list<T>(t);
        (1 + len_t == len && is_good_t, len)

    }
  }

  function length<T>(l: list<T>): (len: int)
    requires (check_list<T>(l)).0 == true;
    ensures (check_list<T>(l).1 == len)
  {
    match l {
      case Nil => 0
      case Cons (h, t, n) => n
    }
  }
}
