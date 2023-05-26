module Matching {
  datatype pattern = Pattern(field: string, value: string)
  datatype record = Empty | Cons(field: string, value: string, tl: record)

  function hasMatchingField(r: record, p: pattern): bool {
    match r {
      case Empty => false
      case Cons(f, v, tl) =>
        if p.field == f then 
           p.value == v
        else 
            hasMatchingField(tl, p)
    }
  }
}
