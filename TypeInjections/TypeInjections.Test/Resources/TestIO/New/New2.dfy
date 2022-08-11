include "New1.dfy"

module New.New2{
  import New1

  datatype nullableOption<T> = Null | Original(o:New1.option<T>)
}