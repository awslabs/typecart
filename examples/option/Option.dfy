module Options {
  datatype {:rust "option", "Option"} Option<+U> = None | Some(val: U) {
    function FMap<V>(f: U -> V): Option<V> {
      match this
      case None => None
      case Some(x) => Some(f(x))
    }

    function Fold<V>(default: V, f: U -> V): V {
      match this
      case None => default
      case Some(x) => f(x)
    }

    function Option(default: U): U {
      Fold(default, x => x)
    }

    function GetOrElse(default: U): U {
      Option(default)
    }
  }
}
