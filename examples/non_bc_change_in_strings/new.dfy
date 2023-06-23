// types unchanged, function headers unchanged
// but function body changed in a way that falsifies the generated backwards-compatibility lemma
module Matching {
  datatype pattern = Pattern(field: string, value: string)
  datatype record = Empty | Cons(field: string, value: string, tl: record)

  function hasMatchingField(r: record, p: pattern): bool {
    match r {
      case Empty => false
      case Cons(f, v, tl) =>
        if p.field == f then
          (p.value == "*") || (p.value == v)
        else
          hasMatchingField(tl, p)
    }
  }
}
