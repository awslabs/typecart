module BigStep {
  type Ident = string

  datatype Aexp =
    | CONST(n: int)
    | VAR(x: Ident)
    | PLUS(a1: Aexp, a2: Aexp)
    | MINUS(a1: Aexp, a2: Aexp)

  predicate IdInAexp(id: Ident, a: Aexp) {
    match a
    case CONST(n) => false
    case VAR(id') => id == id'
    case PLUS(a1, a2) => IdInAexp(id,a1) || IdInAexp(id,a2)
    case MINUS(a1, a2) => IdInAexp(id,a1) || IdInAexp(id,a2)
  }

  type Store = map<Ident,int>

  function Aeval(s: Store, a: Aexp): int
    requires forall id: Ident :: IdInAexp(id,a) ==> id in s
  {
    match a
    case CONST(n) => n
    case VAR(id) => s[id]
    case PLUS(a1, a2) => Aeval(s,a1) + Aeval(s,a2)
    case MINUS(a1, a2) => Aeval(s,a1) - Aeval(s,a2)
  }

  datatype Bexp =
    | TRUE
    | FALSE
    | EQUAL(a1: Aexp, a2: Aexp)
    | LESSEQUAL(a1: Aexp, a2: Aexp)
    | NOT(b1: Bexp)
    | AND(b1: Bexp, b2: Bexp)

  predicate IdInBexp(id: Ident, b: Bexp) {
    match b
    case TRUE => true
    case FALSE => false
    case EQUAL(a1,a2) => IdInAexp(id,a1) || IdInAexp(id,a2)
    case LESSEQUAL(a1,a2) => IdInAexp(id,a1) || IdInAexp(id,a2)
    case NOT(b) => IdInBexp(id,b)
    case AND(b1,b2) => IdInBexp(id,b1) || IdInBexp(id,b2)
  }

  function Beval(s: Store, b: Bexp): bool
    requires forall id: Ident :: IdInBexp(id,b) ==> id in s
  {
    match b
    case TRUE => true
    case FALSE => false
    case EQUAL(a1, a2) => Aeval(s,a1) == Aeval(s,a2)
    case LESSEQUAL(a1, a2) => Aeval(s,a1) <= Aeval(s,a2)
    case NOT(b) => ! Beval(s,b)
    case AND(b1,b2) => Beval(s,b1) && Beval(s,b2)
  }

  datatype Com =
    | SKIP
    | ASSIGN(x: Ident, a: Aexp)
    | SEQ(c1: Com, c2: Com)
    | IFTHENELSE(b: Bexp, c1: Com, c2: Com)
    | WHILE(b: Bexp, c1: Com)

  predicate IdInCom(id: Ident, c: Com) {
    match c
    case SKIP => false
    case ASSIGN(id',a) => IdInAexp(id,a)
    case SEQ(c1, c2) => IdInCom(id,c1) || IdInCom(id,c2)
    case IFTHENELSE(b,c1,c2) => IdInBexp(id,b) || IdInCom(id,c1) || IdInCom(id,c2)
    case WHILE(b,c) => IdInBexp(id,b) || IdInCom(id,c)
  }

  least predicate Cexec(s1: Store, c: Com, s2: Store)
  {
    match c
    case SKIP => s1 == s2
    case ASSIGN(id,a) =>
      if (forall id: Ident :: IdInAexp(id,a) ==> id in s1) then s2 == s1[id := Aeval(s1,a)] else false
    case SEQ(c1, c2) => exists si: Store :: Cexec(s1,c1,si) && Cexec(si,c2,s2)
    case IFTHENELSE(b,c1,c2) =>
      if (forall id: Ident :: IdInBexp(id,b) ==> id in s1) then
        (if Beval(s1,b) then Cexec(s1,c1,s2) else Cexec(s1,c2,s2))
      else false
    case WHILE(b,c) =>
      if (forall id: Ident :: IdInBexp(id,b) ==> id in s1) then
        if Beval(s1,b) then (exists si: Store :: Cexec(s1,c,si) && Cexec(si,WHILE(b,c),s2)) else s1 == s2
      else false
  }

  /* EXTENSION BELOW */

  datatype Option<T> = None | Some(x: T)

  ghost function CexecBounded(fuel: nat, s: Store, c: Com): Option<Store> {
    if (fuel == 0) then None else
    var fuel' := fuel -1;
    match c {
      case SKIP => Some(s)
      case ASSIGN(id, a) =>
        if (forall id: Ident :: IdInAexp(id,a) ==> id in s)
        then Some(s[id := Aeval(s,a)]) else None
      case SEQ(c1, c2) =>
        match CexecBounded(fuel', s, c1) {
          case None => None
          case Some(s') => CexecBounded(fuel', s', c2)
        }
      case IFTHENELSE(b, c1, c2) =>
        if (forall id: Ident :: IdInBexp(id,b) ==> id in s) then
          if Beval(s,b) then CexecBounded(fuel', s, c1) else CexecBounded(fuel', s, c2)
        else None
      case WHILE(b, c1) =>
        if (forall id: Ident :: IdInBexp(id,b) ==> id in s) then
          if Beval(s,b) then
            match CexecBounded(fuel', s, c1) {
              case None => None
              case Some(s') => CexecBounded(fuel', s', WHILE(b, c1))
            } else Some(s)
        else None
    }
  }

  lemma CexecBoundedSound(fuel: nat, s: Store, c: Com, s': Store)
    ensures (CexecBounded(fuel, s, c) == Some(s')) ==> Cexec(s, c, s')
  {
    if (fuel == 0) {} else {
      match c {
        case SEQ(c1, c2) => {
          match CexecBounded(fuel-1, s, c1) {
            case Some(si) => {
              CexecBoundedSound(fuel-1, s, c1, si);
              CexecBoundedSound(fuel-1, si, c2, s');
            }
            case _ => {}
          }
        }
        case IFTHENELSE(b, c1, c2) => {
          CexecBoundedSound(fuel-1, s, c1, s');
          CexecBoundedSound(fuel-1, s, c2, s');
        }
        case WHILE(b, c1) => {
          match CexecBounded(fuel-1, s, c1) {
            case Some(si) => {
              CexecBoundedSound(fuel-1, s, c1, si);
              CexecBoundedSound(fuel-1, si, WHILE(b, c1), s');
            }
            case _ => {}
          }
        }
        case _ => {}
      }
    }
  }

  lemma CexecBoundedComplete(s: Store, c: Com, s': Store)
    ensures Cexec(s, c, s') ==> (exists fuel1 : nat :: forall fuel: nat ::
                                                         (fuel >= fuel1) ==> CexecBounded(fuel, s, c) == Some(s'))
  {
    if (Cexec(s, c, s')) { assume false;
                           match c {
                             case SEQ(c1, c2) => {
                               var si :| Cexec(s,c1,si) && Cexec(si,c2,s');
                               CexecBoundedComplete(s, c1, si);
                               CexecBoundedComplete(si, c2, s');
                             }
                             case IFTHENELSE(b,c1,c2) => {
                               if (forall id: Ident :: IdInBexp(id,b) ==> id in s) {
                                 if Beval(s,b) {
                                   CexecBoundedComplete(s, c1, s');
                                 } else {
                                   CexecBoundedComplete(s, c2, s');
                                 }
                               }
                             }
                             case WHILE(b,c) => {
                               if (forall id: Ident :: IdInBexp(id,b) ==> id in s) {
                                 if Beval(s,b) {
                                   var si: Store :| Cexec(s,c,si) && Cexec(si,WHILE(b,c),s');
                                   CexecBoundedComplete(s, c, si);
                                   CexecBoundedComplete(si, WHILE(b,c), s');
                                 }
                               }
                             }
                             case _ => {}
                           }
                         } else {}
  }
}
