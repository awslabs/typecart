include "Old1.dfy"

module Old.Old2{
  import Old1

  datatype nullableOption<T> = Null | Original(o:Old1.option<T>)
}