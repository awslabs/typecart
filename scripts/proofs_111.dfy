include "joint.dfy"
include "old.dfy"
include "new.dfy"
/***** TYPECART PRELUDE START *****/
module Translations.MapBuiltinTypes {
  function Seq<o,n>(t: o -> n, e: seq<o>) : (f : seq<n>)
    ensures |e| == |f|
    ensures forall i : int :: (0 <= i < |e| ==> f[i] == t(e[i]))
  {
    if e == [] then [] else [t(e[0])] + Seq(t, e[1..])
  }
  function Set<o,n>(t: o -> n, e: set<o>) : (f : set<n>)
    ensures forall x : o :: x in e ==> t(x) in f
    ensures forall x : n :: x in f ==> exists y : o :: y in e && t(y) == x
  {
    set x:o | x in e :: t(x)
  }
  /* We need a translation function from K_N to K_O in order to translate from map<K_O, V_O> to map<K_N, V_N>.
   * For example, if we want to translate sqr(x) = x * x from map<real, real> to map<int, int>
   * where K(x) = round(x), we need K2(x) = x * 1.0 so that sqr(1.4) = 1.96 is translated to
   * sqr(round(1.4)) = (round(1.4) * 1.0) * (round(1.4) * 1.0), i.e., sqr(1) = 1,
   * instead of sqr(round(1.4)) = round(1.4 * 1.4), i.e., sqr(1) = 2.
   */
  function Map<K_O,K_N(==),V_O,V_N(==)>(K: K_O -> K_N, K2: K_N -> K_O, V: V_O -> V_N, e: map<K_O, V_O>) : (f: map<K_N, V_N>)
  {
    var fKeys := set x: K_O | x in e.Keys && K2(K(x)) in e.Keys :: K(x);
    map a | a in fKeys :: V(e[K2(a)])
  }
}

module Translations.Utils {
  /* We requires false here because Dafny 4 does not allow non-determinism like ":|" in functions.
   * This function is to convert name resolution errors in stubs generated in translation functions
   * to verification errors (cannot prove false), so Dafny will not stop verifying the entire program
   * when it sees "???".
   */
  function ???<X(0)>(): X
    requires false
  {
    var tmp: X :| true;
    tmp
  }
}

/***** TYPECART PRELUDE END *****/





module Proofs {
  import Joint

  import Old

  import New

  import Translations

  module validation {
    import Joint

    import Old

    import New

    import Translations

    module util {
      import Joint

      import Old

      import New

      import Translations

      lemma {:axiom} substitute_bc(e_O: Joint.def.core.Expr, v_O: Joint.def.core.Var, euid_O: Joint.def.core.EntityUID, e_N: Joint.def.core.Expr, v_N: Joint.def.core.Var, euid_N: Joint.def.core.EntityUID)
        decreases e_O, v_O, euid_O
        requires e_N == e_O
        requires v_N == v_O
        requires euid_N == euid_O
        ensures New.validation.util.substitute(e_N, v_N, euid_N) == Old.validation.util.substitute(e_O, v_O, euid_O)

      import opened def.base

      import opened def.core

      import opened def.engine
    }

    module types {
      import Joint

      import Old

      import New

      import Translations

      lemma {:axiom} isAction_bc(ety_O: Old.validation.types.EntityType, ety_N: New.validation.types.EntityType)
        decreases ety_O
        requires ety_N == EntityType_forward(ety_O)
        ensures New.validation.types.isAction(ety_N) == Old.validation.types.isAction(ety_O)

      lemma Ok_bc<T_O, T_N>(T_forward: T_O->T_N, T_backward: T_N->T_O, v_O: T_O, v_N: T_N)
        requires v_N == T_forward(v_O)
        requires forall x_O: T_O :: T_backward(T_forward(x_O)) == x_O
        ensures New.validation.types.Ok(v_N) == Result_forward(T_forward, T_backward, Old.validation.types.Ok(v_O))
      {
        assert New.validation.types.Ok(v_N) == Result_forward(T_forward, T_backward, Joint.def.std.Result.Ok(v_O));
      }

      lemma Err_bc<T_O, T_N>(T_forward: T_O->T_N, T_backward: T_N->T_O, v_O: Old.validation.types.TypeError, v_N: New.validation.types.TypeError)
        decreases v_O
        requires v_N == TypeError_forward(v_O)
        requires forall x_O: T_O :: T_backward(T_forward(x_O)) == x_O
        ensures New.validation.types.Err(v_N) == Result_forward(T_forward, T_backward, Old.validation.types.Err(v_O))
      {
        assert New.validation.types.Err(v_N) == Result_forward(T_forward, T_backward, Joint.def.std.Result.Err(v_O));
      }

      import opened def.base

      import opened def.core

      function BoolType_forward(B_O: Old.validation.types.BoolType): New.validation.types.BoolType
      {
        match B_O {
          case AnyBool() =>
            /* unchanged constructor */ New.validation.types.BoolType.AnyBool()
          case True() =>
            /* unchanged constructor */ New.validation.types.BoolType.True()
          case False() =>
            /* unchanged constructor */ New.validation.types.BoolType.False()
        }
      }

      function BoolType_backward(B_N: New.validation.types.BoolType): Old.validation.types.BoolType
      {
        match B_N {
          case AnyBool() =>
            /* unchanged constructor */ Old.validation.types.BoolType.AnyBool()
          case True() =>
            /* unchanged constructor */ Old.validation.types.BoolType.True()
          case False() =>
            /* unchanged constructor */ Old.validation.types.BoolType.False()
        }
      }

      lemma {:axiom} BoolType_not_bc(B_O: Old.validation.types.BoolType, B_N: New.validation.types.BoolType)
        decreases B_O
        requires B_N == BoolType_forward(B_O)
        ensures B_N.not() == BoolType_forward(B_O.not())

      function EntityType_forward(E_O: Old.validation.types.EntityType): New.validation.types.EntityType
      {
        E_O
      }

      function EntityType_backward(E_N: New.validation.types.EntityType): Old.validation.types.EntityType
      {
        E_N
      }

      function EntityLUB_forward(E_O: Old.validation.types.EntityLUB): New.validation.types.EntityLUB
      {
        match E_O {
          case AnyEntity() =>
            /* unchanged constructor */ New.validation.types.EntityLUB.AnyEntity()
          case EntityLUB(tys_O) =>
            /* unchanged constructor */ New.validation.types.EntityLUB.EntityLUB(Translations.MapBuiltinTypes.Set((st: Old.validation.types.EntityType) => EntityType_forward(st), tys_O))
        }
      }

      function EntityLUB_backward(E_N: New.validation.types.EntityLUB): Old.validation.types.EntityLUB
      {
        match E_N {
          case AnyEntity() =>
            /* unchanged constructor */ Old.validation.types.EntityLUB.AnyEntity()
          case EntityLUB(tys_N) =>
            /* unchanged constructor */ Old.validation.types.EntityLUB.EntityLUB(Translations.MapBuiltinTypes.Set((st: New.validation.types.EntityType) => EntityType_backward(st), tys_N))
        }
      }

      lemma EntityLUB_subset_bc(E_O: Old.validation.types.EntityLUB, E_N: New.validation.types.EntityLUB, other_O: Old.validation.types.EntityLUB, other_N: New.validation.types.EntityLUB)
        decreases E_O, other_O
        requires E_N == EntityLUB_forward(E_O)
        requires other_N == EntityLUB_forward(other_O)
        ensures E_N.subset(other_N) == E_O.subset(other_O)
      {
        match (E_O, other_O) {
          case (_, AnyEntity()) =>
            assert E_N.subset(other_N) == true;
          case (EntityLUB(tys1), EntityLUB(tys2)) =>
            assert E_N.subset(other_N) == (tys1 <= tys2);
          case _ =>
            assert E_N.subset(other_N) == false;
        }
      }

      lemma EntityLUB_disjoint_bc(E_O: Old.validation.types.EntityLUB, E_N: New.validation.types.EntityLUB, other_O: Old.validation.types.EntityLUB, other_N: New.validation.types.EntityLUB)
        decreases E_O, other_O
        requires E_N == EntityLUB_forward(E_O)
        requires other_N == EntityLUB_forward(other_O)
        ensures E_N.disjoint(other_N) == E_O.disjoint(other_O)
      {
        match (E_O, other_O) {
          case (EntityLUB(tys1), EntityLUB(tys2)) =>
            assert E_N.disjoint(other_N) == (tys1 !! tys2);
          case _ =>
            assert E_N.disjoint(other_N) == false;
        }
      }

      lemma EntityLUB_union_bc(E_O: Old.validation.types.EntityLUB, E_N: New.validation.types.EntityLUB, other_O: Old.validation.types.EntityLUB, other_N: New.validation.types.EntityLUB)
        decreases E_O, other_O
        requires E_N == EntityLUB_forward(E_O)
        requires other_N == EntityLUB_forward(other_O)
        ensures E_N.union(other_N) == EntityLUB_forward(E_O.union(other_O))
      {
        match (E_O, other_O) {
          case (EntityLUB(tys1), EntityLUB(tys2)) =>
            if (exists ty1: Old.validation.types.EntityType ::
              ty1 in tys1 && ((isAction_bc(ty1, EntityType_forward(ty1));
              Old.validation.types.isAction(ty1)) || (exists ty2: Old.validation.types.EntityType ::
                ty2 in tys2 && (isAction_bc(ty2, EntityType_forward(ty2));
                Old.validation.types.isAction(ty2))))) {
              assert E_N.union(other_N) == EntityLUB_forward(Old.validation.types.EntityLUB.AnyEntity());
            } else {
              assert E_N.union(other_N) == EntityLUB_forward(Old.validation.types.EntityLUB.EntityLUB(tys1 + tys2));
            }
          case _ =>
            assert E_N.union(other_N) == EntityLUB_forward(Old.validation.types.EntityLUB.AnyEntity());
        }
      }

      lemma EntityLUB_specified_bc(E_O: Old.validation.types.EntityLUB, E_N: New.validation.types.EntityLUB)
        decreases E_O
        requires E_N == EntityLUB_forward(E_O)
        ensures E_N.specified() == E_O.specified()
      {
        assert E_N.specified() == (E_O.EntityLUB? && Joint.def.core.EntityType.UNSPECIFIED !in E_O.tys);
      }

      function AttrType_forward(A_O: Old.validation.types.AttrType): New.validation.types.AttrType
      {
        match A_O {
          case AttrType(ty_O, isRequired_O) =>
            /* unchanged constructor */ New.validation.types.AttrType.AttrType(Type_forward(ty_O), isRequired_O)
        }
      }

      function AttrType_backward(A_N: New.validation.types.AttrType): Old.validation.types.AttrType
      {
        match A_N {
          case AttrType(ty_N, isRequired_N) =>
            /* unchanged constructor */ Old.validation.types.AttrType.AttrType(Type_backward(ty_N), isRequired_N)
        }
      }

      function AttrsTag_forward(A_O: Old.validation.types.AttrsTag): New.validation.types.AttrsTag
      {
        match A_O {
          case OpenAttributes() =>
            /* unchanged constructor */ New.validation.types.AttrsTag.OpenAttributes()
          case ClosedAttributes() =>
            /* unchanged constructor */ New.validation.types.AttrsTag.ClosedAttributes()
        }
      }

      function AttrsTag_backward(A_N: New.validation.types.AttrsTag): Old.validation.types.AttrsTag
      {
        match A_N {
          case OpenAttributes() =>
            /* unchanged constructor */ Old.validation.types.AttrsTag.OpenAttributes()
          case ClosedAttributes() =>
            /* unchanged constructor */ Old.validation.types.AttrsTag.ClosedAttributes()
        }
      }

      function RecordType_forward(R_O: Old.validation.types.RecordType): New.validation.types.RecordType
      {
        match R_O {
          case RecordType(attrs_O, attrsTag_O) =>
            /* unchanged constructor */ New.validation.types.RecordType.RecordType(Translations.MapBuiltinTypes.Map((mp: Joint.def.core.Attr) => mp, (mp: Joint.def.core.Attr) => mp, (mp: Old.validation.types.AttrType) => AttrType_forward(mp), attrs_O), AttrsTag_forward(attrsTag_O))
        }
      }

      function RecordType_backward(R_N: New.validation.types.RecordType): Old.validation.types.RecordType
      {
        match R_N {
          case RecordType(attrs_N, attrsTag_N) =>
            /* unchanged constructor */ Old.validation.types.RecordType.RecordType(Translations.MapBuiltinTypes.Map((mp: Joint.def.core.Attr) => mp, (mp: Joint.def.core.Attr) => mp, (mp: New.validation.types.AttrType) => AttrType_backward(mp), attrs_N), AttrsTag_backward(attrsTag_N))
        }
      }

      lemma RecordType_isOpen_bc(R_O: Old.validation.types.RecordType, R_N: New.validation.types.RecordType)
        decreases R_O
        requires R_N == RecordType_forward(R_O)
        ensures R_N.isOpen() == R_O.isOpen()
      {
        assert R_N.isOpen() == R_O.attrsTag.OpenAttributes?;
      }

      function ExtFunType_forward(E_O: Old.validation.types.ExtFunType): New.validation.types.ExtFunType
      {
        match E_O {
          case ExtFunType(args_O, ret_O, check_O) =>
            /* unchanged constructor */ New.validation.types.ExtFunType.ExtFunType(Translations.MapBuiltinTypes.Seq((sq: Old.validation.types.Type) => Type_forward(sq), args_O), Type_forward(ret_O), Option_forward((x: seq<Joint.def.core.Expr>->Old.validation.types.Result<()>) => (x1_N: seq<Joint.def.core.Expr>) => Result_forward((x: ()) => (), (x: ()) => (), x(x1_N)), (x: seq<Joint.def.core.Expr>->New.validation.types.Result<()>) => (x1_O: seq<Joint.def.core.Expr>) => Result_backward((x: ()) => (), (x: ()) => (), x(x1_O)), check_O))
        }
      }

      function ExtFunType_backward(E_N: New.validation.types.ExtFunType): Old.validation.types.ExtFunType
      {
        match E_N {
          case ExtFunType(args_N, ret_N, check_N) =>
            /* unchanged constructor */ Old.validation.types.ExtFunType.ExtFunType(Translations.MapBuiltinTypes.Seq((sq: New.validation.types.Type) => Type_backward(sq), args_N), Type_backward(ret_N), Option_backward((x: seq<Joint.def.core.Expr>->Old.validation.types.Result<()>) => (x1_N: seq<Joint.def.core.Expr>) => Result_forward((x: ()) => (), (x: ()) => (), x(x1_N)), (x: seq<Joint.def.core.Expr>->New.validation.types.Result<()>) => (x1_O: seq<Joint.def.core.Expr>) => Result_backward((x: ()) => (), (x: ()) => (), x(x1_O)), check_N))
        }
      }

      function Type_forward(T_O: Old.validation.types.Type): New.validation.types.Type
      {
        match T_O {
          case Never() =>
            /* unchanged constructor */ New.validation.types.Type.Never()
          case String() =>
            /* unchanged constructor */ New.validation.types.Type.String()
          case Int() =>
            /* unchanged constructor */ New.validation.types.Type.Int()
          case Bool(x4_O) =>
            /* unchanged constructor */ New.validation.types.Type.Bool(BoolType_forward(x4_O))
          case Set(ty_O) =>
            /* unchanged constructor */ New.validation.types.Type.Set(Type_forward(ty_O))
          case Record(x5_O) =>
            /* unchanged constructor */ New.validation.types.Type.Record(RecordType_forward(x5_O))
          case Entity(lub_O) =>
            /* unchanged constructor */ New.validation.types.Type.Entity(EntityLUB_forward(lub_O))
          case Extension(x6_O) =>
            /* unchanged constructor */ New.validation.types.Type.Extension(x6_O)
        }
      }

      function Type_backward(T_N: New.validation.types.Type): Old.validation.types.Type
      {
        match T_N {
          case Never() =>
            /* unchanged constructor */ Old.validation.types.Type.Never()
          case String() =>
            /* unchanged constructor */ Old.validation.types.Type.String()
          case Int() =>
            /* unchanged constructor */ Old.validation.types.Type.Int()
          case Bool(x4_N) =>
            /* unchanged constructor */ Old.validation.types.Type.Bool(BoolType_backward(x4_N))
          case Set(ty_N) =>
            /* unchanged constructor */ Old.validation.types.Type.Set(Type_backward(ty_N))
          case Record(x5_N) =>
            /* unchanged constructor */ Old.validation.types.Type.Record(RecordType_backward(x5_N))
          case Entity(lub_N) =>
            /* unchanged constructor */ Old.validation.types.Type.Entity(EntityLUB_backward(lub_N))
          case Extension(x6_N) =>
            /* unchanged constructor */ Old.validation.types.Type.Extension(x6_N)
        }
      }

      function SetStringType_forward(S_O: Old.validation.types.SetStringType): New.validation.types.SetStringType
      {
        match S_O {
          case SetType(x7_O) =>
            /* added/deleted/updated constructor arguments */ New.validation.types.SetStringType.SetType(Type_forward(x7_O))
          case StringType() =>
            /* unchanged constructor */ New.validation.types.SetStringType.StringType()
        }
      }

      function SetStringType_backward(S_N: New.validation.types.SetStringType): Old.validation.types.SetStringType
      {
        match S_N {
          case SetType(x9_N) =>
            /* added/deleted/updated constructor arguments */ Old.validation.types.SetStringType.SetType(Type_backward(x9_N))
          case StringType() =>
            /* unchanged constructor */ Old.validation.types.SetStringType.StringType()
        }
      }

      function RecordEntityType_forward(R_O: Old.validation.types.RecordEntityType): New.validation.types.RecordEntityType
      {
        match R_O {
          case Record(x8_O) =>
            /* added/deleted/updated constructor arguments */ New.validation.types.RecordEntityType.Record(RecordType_forward(x8_O))
          case Entity(x9_O) =>
            /* added/deleted/updated constructor arguments */ New.validation.types.RecordEntityType.Entity(EntityLUB_forward(x9_O))
        }
      }

      function RecordEntityType_backward(R_N: New.validation.types.RecordEntityType): Old.validation.types.RecordEntityType
      {
        match R_N {
          case Record(x10_N) =>
            /* added/deleted/updated constructor arguments */ Old.validation.types.RecordEntityType.Record(RecordType_backward(x10_N))
          case Entity(x11_N) =>
            /* added/deleted/updated constructor arguments */ Old.validation.types.RecordEntityType.Entity(EntityLUB_backward(x11_N))
        }
      }

      function TypeError_forward(T_O: Old.validation.types.TypeError): New.validation.types.TypeError
      {
        match T_O {
          case LubErr(x10_O, x11_O) =>
            /* added/deleted/updated constructor arguments */ New.validation.types.TypeError.LubErr(Type_forward(x10_O), Type_forward(x11_O))
          case SubtyErr(x12_O, x13_O) =>
            /* added/deleted/updated constructor arguments */ New.validation.types.TypeError.SubtyErr(Type_forward(x12_O), Type_forward(x13_O))
          case UnexpectedType(x14_O) =>
            /* added/deleted/updated constructor arguments */ New.validation.types.TypeError.UnexpectedType(Type_forward(x14_O))
          case AttrNotFound(x15_O, x16_O) =>
            /* added/deleted/updated constructor arguments */ New.validation.types.TypeError.AttrNotFound(Type_forward(x15_O), x16_O)
          case UnknownEntities(x17_O) =>
            /* added/deleted/updated constructor arguments */ New.validation.types.TypeError.UnknownEntities(Translations.MapBuiltinTypes.Set((st: Old.validation.types.EntityType) => EntityType_forward(st), x17_O))
          case ExtensionErr(x18_O) =>
            /* added/deleted/updated constructor arguments */ New.validation.types.TypeError.ExtensionErr(x18_O)
          case EmptyLUB() =>
            /* unchanged constructor */ New.validation.types.TypeError.EmptyLUB()
        }
      }

      function TypeError_backward(T_N: New.validation.types.TypeError): Old.validation.types.TypeError
      {
        match T_N {
          case LubErr(x12_N, x13_N) =>
            /* added/deleted/updated constructor arguments */ Old.validation.types.TypeError.LubErr(Type_backward(x12_N), Type_backward(x13_N))
          case SubtyErr(x14_N, x15_N) =>
            /* added/deleted/updated constructor arguments */ Old.validation.types.TypeError.SubtyErr(Type_backward(x14_N), Type_backward(x15_N))
          case UnexpectedType(x16_N) =>
            /* added/deleted/updated constructor arguments */ Old.validation.types.TypeError.UnexpectedType(Type_backward(x16_N))
          case AttrNotFound(x17_N, x18_N) =>
            /* added/deleted/updated constructor arguments */ Old.validation.types.TypeError.AttrNotFound(Type_backward(x17_N), x18_N)
          case UnknownEntities(x19_N) =>
            /* added/deleted/updated constructor arguments */ Old.validation.types.TypeError.UnknownEntities(Translations.MapBuiltinTypes.Set((st: New.validation.types.EntityType) => EntityType_backward(st), x19_N))
          case ExtensionErr(x20_N) =>
            /* added/deleted/updated constructor arguments */ Old.validation.types.TypeError.ExtensionErr(x20_N)
          case EmptyLUB() =>
            /* unchanged constructor */ Old.validation.types.TypeError.EmptyLUB()
          case EmptySetForbidden() =>
            /* deleted constructor */ Translations.Utils.???()
          case NonLitExtConstructor() =>
            /* deleted constructor */ Translations.Utils.???()
          case NonSingletonLub() =>
            /* deleted constructor */ Translations.Utils.???()
          case HierarchyNotRespected() =>
            /* deleted constructor */ Translations.Utils.???()
        }
      }

      function Result_forward<T_O, T_N>(T_forward: T_O->T_N, T_backward: T_N->T_O, R_O: Old.validation.types.Result<T_O>): New.validation.types.Result<T_N>
      {
        std.Result_forward(T_forward, T_backward, (x: Old.validation.types.TypeError) => TypeError_forward(x), (x: New.validation.types.TypeError) => TypeError_backward(x), R_O)
      }

      function Result_backward<T_O, T_N>(T_forward: T_O->T_N, T_backward: T_N->T_O, R_N: New.validation.types.Result<T_N>): Old.validation.types.Result<T_O>
      {
        std.Result_backward(T_forward, T_backward, (x: Old.validation.types.TypeError) => TypeError_forward(x), (x: New.validation.types.TypeError) => TypeError_backward(x), R_N)
      }

      function Option_forward<T_O, T_N>(T_forward: T_O->T_N, T_backward: T_N->T_O, O_O: Old.validation.types.Option<T_O>): New.validation.types.Option<T_N>
      {
        std.Option_forward(T_forward, T_backward, O_O)
      }

      function Option_backward<T_O, T_N>(T_forward: T_O->T_N, T_backward: T_N->T_O, O_N: New.validation.types.Option<T_N>): Old.validation.types.Option<T_O>
      {
        std.Option_backward(T_forward, T_backward, O_N)
      }
    }

    module subtyping {
      import Joint

      import Old

      import New

      import Translations

      lemma {:axiom} subtyBool_bc(b1_O: Old.validation.types.BoolType, b2_O: Old.validation.types.BoolType, b1_N: New.validation.types.BoolType, b2_N: New.validation.types.BoolType)
        decreases b1_O, b2_O
        requires b1_N == BoolType_forward(b1_O)
        requires b2_N == BoolType_forward(b2_O)
        ensures New.validation.subtyping.subtyBool(b1_N, b2_N) == Old.validation.subtyping.subtyBool(b1_O, b2_O)

      lemma subtyAttrType_bc(a1_O: Old.validation.types.AttrType, a2_O: Old.validation.types.AttrType, a1_N: New.validation.types.AttrType, a2_N: New.validation.types.AttrType, m_N: New.validation.types.ValidationMode)
        decreases a1_O, a2_O
        requires a1_N == AttrType_forward(a1_O)
        requires a2_N == AttrType_forward(a2_O)
        ensures New.validation.subtyping.subtyAttrType(a1_N, a2_N, m_N) == Old.validation.subtyping.subtyAttrType(a1_O, a2_O)
      {
        assert New.validation.subtyping.subtyAttrType(a1_N, a2_N, m_N) == (Old.validation.subtyping.subty(a1_O.ty, a2_O.ty) && (a2_O.isRequired ==> a1_O.isRequired));
      }

      lemma subtyRecordType_bc(rt1_O: Old.validation.types.RecordType, rt2_O: Old.validation.types.RecordType, rt1_N: New.validation.types.RecordType, rt2_N: New.validation.types.RecordType, m_N: New.validation.types.ValidationMode)
        decreases Old.validation.types.Type.Record(rt1_O), Old.validation.types.Type.Record(rt2_O), 0
        requires rt1_N == RecordType_forward(rt1_O)
        requires rt2_N == RecordType_forward(rt2_O)
        ensures New.validation.subtyping.subtyRecordType(rt1_N, rt2_N, m_N) == Old.validation.subtyping.subtyRecordType(rt1_O, rt2_O)
      {
        assert New.validation.subtyping.subtyRecordType(rt1_N, rt2_N, m_N) == (((RecordType_isOpen_bc(rt1_O, rt1_N);
        rt1_O.isOpen()) ==> (RecordType_isOpen_bc(rt2_O, rt2_N);
        rt2_O.isOpen())) && rt2_O.attrs.Keys <= rt1_O.attrs.Keys && (forall k: string :: k in rt2_O.attrs.Keys ==> Old.validation.subtyping.subtyAttrType(rt1_O.attrs[k], rt2_O.attrs[k])) && (!(RecordType_isOpen_bc(rt2_O, rt2_N);
        rt2_O.isOpen()) ==> rt1_O.attrs.Keys == rt2_O.attrs.Keys));
      }

      lemma subtyEntity_bc(lub1_O: Old.validation.types.EntityLUB, lub2_O: Old.validation.types.EntityLUB, lub1_N: New.validation.types.EntityLUB, lub2_N: New.validation.types.EntityLUB, m_N: New.validation.types.ValidationMode)
        decreases lub1_O, lub2_O
        requires lub1_N == EntityLUB_forward(lub1_O)
        requires lub2_N == EntityLUB_forward(lub2_O)
        ensures New.validation.subtyping.subtyEntity(lub1_N, lub2_N, m_N) == Old.validation.subtyping.subtyEntity(lub1_O, lub2_O)
      {
        EntityLUB_subset_bc(lub1_O, lub1_N, lub2_O, lub2_N);
        assert New.validation.subtyping.subtyEntity(lub1_N, lub2_N, m_N) == lub1_O.subset(lub2_O);
      }

      lemma subty_bc(t1_O: Old.validation.types.Type, t2_O: Old.validation.types.Type, t1_N: New.validation.types.Type, t2_N: New.validation.types.Type, m_N: New.validation.types.ValidationMode)
        decreases t1_O, t2_O
        requires t1_N == Type_forward(t1_O)
        requires t2_N == Type_forward(t2_O)
        ensures New.validation.subtyping.subty(t1_N, t2_N, m_N) == Old.validation.subtyping.subty(t1_O, t2_O)
      {
        match (t1_O, t2_O) {
          case (Never(), _) =>
            assert New.validation.subtyping.subty(t1_N, t2_N, m_N) == true;
          case (String(), String()) =>
            assert New.validation.subtyping.subty(t1_N, t2_N, m_N) == true;
          case (Int(), Int()) =>
            assert New.validation.subtyping.subty(t1_N, t2_N, m_N) == true;
          case (Bool(b1), Bool(b2)) =>
            subtyBool_bc(b1, b2, BoolType_forward(b1), BoolType_forward(b2));
            assert New.validation.subtyping.subty(t1_N, t2_N, m_N) == Old.validation.subtyping.subtyBool(b1, b2);
          case (Set(t11), Set(t21)) =>
            assert New.validation.subtyping.subty(t1_N, t2_N, m_N) == Old.validation.subtyping.subty(t11, t21);
          case (Record(rt1), Record(rt2)) =>
            assert New.validation.subtyping.subty(t1_N, t2_N, m_N) == Old.validation.subtyping.subtyRecordType(rt1, rt2);
          case (Entity(lub1), Entity(lub2)) =>
            assert New.validation.subtyping.subty(t1_N, t2_N, m_N) == Old.validation.subtyping.subtyEntity(lub1, lub2);
          case (Extension(e1), Extension(e2)) =>
            assert New.validation.subtyping.subty(t1_N, t2_N, m_N) == (e1 == e2);
          case _ =>
            assert New.validation.subtyping.subty(t1_N, t2_N, m_N) == false;
        }
      }

      lemma {:axiom} lubBool_bc(b1_O: Old.validation.types.BoolType, b2_O: Old.validation.types.BoolType, b1_N: New.validation.types.BoolType, b2_N: New.validation.types.BoolType)
        decreases b1_O, b2_O
        requires b1_N == BoolType_forward(b1_O)
        requires b2_N == BoolType_forward(b2_O)
        ensures New.validation.subtyping.lubBool(b1_N, b2_N) == BoolType_forward(Old.validation.subtyping.lubBool(b1_O, b2_O))

      lemma lubEntity_bc(lub1_O: Old.validation.types.EntityLUB, lub2_O: Old.validation.types.EntityLUB, lub1_N: New.validation.types.EntityLUB, lub2_N: New.validation.types.EntityLUB, m_N: New.validation.types.ValidationMode)
        decreases lub1_O, lub2_O
        requires lub1_N == EntityLUB_forward(lub1_O)
        requires lub2_N == EntityLUB_forward(lub2_O)
        ensures /* cannot translate output type */ false
      {}

      lemma lubAttrType_bc(a1_O: Old.validation.types.AttrType, a2_O: Old.validation.types.AttrType, a1_N: New.validation.types.AttrType, a2_N: New.validation.types.AttrType, m_N: New.validation.types.ValidationMode)
        decreases a1_O, a2_O
        requires Old.validation.subtyping.lubOpt(a1_O.ty, a2_O.ty).Ok?
        requires a1_N == AttrType_forward(a1_O)
        requires a2_N == AttrType_forward(a2_O)
        ensures New.validation.subtyping.lubOpt(a1_N.ty, a2_N.ty, m_N).Ok?
        ensures New.validation.subtyping.lubAttrType(a1_N, a2_N, m_N) == AttrType_forward(Old.validation.subtyping.lubAttrType(a1_O, a2_O))
      {
        assert New.validation.subtyping.lubAttrType(a1_N, a2_N, m_N) == AttrType_forward(Old.validation.types.AttrType.AttrType(Old.validation.subtyping.lubOpt(a1_O.ty, a2_O.ty).value, a1_O.isRequired && a2_O.isRequired));
      }

      lemma lubRecordType_bc(rt1_O: Old.validation.types.RecordType, rt2_O: Old.validation.types.RecordType, rt1_N: New.validation.types.RecordType, rt2_N: New.validation.types.RecordType, m_N: New.validation.types.ValidationMode)
        decreases Old.validation.types.Type.Record(rt1_O), Old.validation.types.Type.Record(rt2_O), 0
        requires rt1_N == RecordType_forward(rt1_O)
        requires rt2_N == RecordType_forward(rt2_O)
        ensures /* cannot translate output type */ false
      {}

      lemma lubRecordTypeSeq_bc(rts_O: seq<Old.validation.types.RecordType>, rts_N: seq<New.validation.types.RecordType>, m_N: New.validation.types.ValidationMode)
        decreases rts_O
        requires rts_N == Translations.MapBuiltinTypes.Seq((sq: Old.validation.types.RecordType) => RecordType_forward(sq), rts_O)
        ensures New.validation.subtyping.lubRecordTypeSeq(rts_N, m_N) == Result_forward((x: Old.validation.types.RecordType) => RecordType_forward(x), (x: New.validation.types.RecordType) => RecordType_backward(x), Old.validation.subtyping.lubRecordTypeSeq(rts_O))
      {
        if (rts_O == []) {
          Err_bc((x: Old.validation.types.RecordType) => RecordType_forward(x), (x: New.validation.types.RecordType) => RecordType_backward(x), Old.validation.types.TypeError.EmptyLUB(), New.validation.types.TypeError.EmptyLUB());
          assert New.validation.subtyping.lubRecordTypeSeq(rts_N, m_N) == Result_forward((x: Old.validation.types.RecordType) => RecordType_forward(x), (x: New.validation.types.RecordType) => RecordType_backward(x), Old.validation.types.Err(Old.validation.types.TypeError.EmptyLUB()));
        } else {
          if (|rts_O| == 1) {
            Ok_bc((x: Old.validation.types.RecordType) => RecordType_forward(x), (x: New.validation.types.RecordType) => RecordType_backward(x), rts_O[0], rts_N[0]);
            assert New.validation.subtyping.lubRecordTypeSeq(rts_N, m_N) == Result_forward((x: Old.validation.types.RecordType) => RecordType_forward(x), (x: New.validation.types.RecordType) => RecordType_backward(x), Old.validation.types.Ok(rts_O[0]));
          } else {
            assert New.validation.subtyping.lubRecordTypeSeq(rts_N, m_N) == Result_forward((x: Old.validation.types.RecordType) => RecordType_forward(x), (x: New.validation.types.RecordType) => RecordType_backward(x), var res :- Old.validation.subtyping.lubRecordTypeSeq(rts_O[1..]);
            Old.validation.types.Ok(Old.validation.subtyping.lubRecordType(rts_O[0], res)));
          }
        }
      }

      lemma lubOpt_bc(t1_O: Old.validation.types.Type, t2_O: Old.validation.types.Type, t1_N: New.validation.types.Type, t2_N: New.validation.types.Type, m_N: New.validation.types.ValidationMode)
        decreases t1_O, t2_O, 1
        requires t1_N == Type_forward(t1_O)
        requires t2_N == Type_forward(t2_O)
        ensures New.validation.subtyping.lubOpt(t1_N, t2_N, m_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.subtyping.lubOpt(t1_O, t2_O))
      {
        match (t1_O, t2_O) {
          case (Never(), _) =>
            Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), t2_O, t2_N);
            assert New.validation.subtyping.lubOpt(t1_N, t2_N, m_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Ok(t2_O));
          case (_, Never()) =>
            Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), t1_O, t1_N);
            assert New.validation.subtyping.lubOpt(t1_N, t2_N, m_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Ok(t1_O));
          case (String(), String()) =>
            Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.String(), New.validation.types.Type.String());
            assert New.validation.subtyping.lubOpt(t1_N, t2_N, m_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Ok(Old.validation.types.Type.String()));
          case (Int(), Int()) =>
            Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Int(), New.validation.types.Type.Int());
            assert New.validation.subtyping.lubOpt(t1_N, t2_N, m_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Ok(Old.validation.types.Type.Int()));
          case (Bool(b1), Bool(b2)) =>
            Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Bool(Old.validation.subtyping.lubBool(b1, b2)), New.validation.types.Type.Bool(New.validation.subtyping.lubBool(BoolType_forward(b1), BoolType_forward(b2))));
            assert New.validation.subtyping.lubOpt(t1_N, t2_N, m_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Ok(Old.validation.types.Type.Bool(lubBool_bc(b1, b2, BoolType_forward(b1), BoolType_forward(b2));
            Old.validation.subtyping.lubBool(b1, b2))));
          case (Entity(lub1), Entity(lub2)) =>
            assert New.validation.subtyping.lubOpt(t1_N, t2_N, m_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Ok(Old.validation.types.Type.Entity(Old.validation.subtyping.lubEntity(lub1, lub2))));
          case (Set(t11), Set(t12)) =>
            assert New.validation.subtyping.lubOpt(t1_N, t2_N, m_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), var t :- Old.validation.subtyping.lubOpt(t11, t12);
            Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Set(t), New.validation.types.Type.Set(Type_forward(t)));
            Old.validation.types.Ok(Old.validation.types.Type.Set(t)));
          case (Record(rt1), Record(rt2)) =>
            assert New.validation.subtyping.lubOpt(t1_N, t2_N, m_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Ok(Old.validation.types.Type.Record(Old.validation.subtyping.lubRecordType(rt1, rt2))));
          case (Extension(e1), Extension(e2)) =>
            if (e1 == e2) {
              Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Extension(e1), New.validation.types.Type.Extension(e1));
              assert New.validation.subtyping.lubOpt(t1_N, t2_N, m_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Ok(Old.validation.types.Type.Extension(e1)));
            } else {
              Err_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.TypeError.LubErr(t1_O, t2_O), New.validation.types.TypeError.LubErr(t1_N, t2_N));
              assert New.validation.subtyping.lubOpt(t1_N, t2_N, m_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Err(Old.validation.types.TypeError.LubErr(t1_O, t2_O)));
            }
          case _ =>
            Err_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.TypeError.LubErr(t1_O, t2_O), New.validation.types.TypeError.LubErr(t1_N, t2_N));
            assert New.validation.subtyping.lubOpt(t1_N, t2_N, m_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Err(Old.validation.types.TypeError.LubErr(t1_O, t2_O)));
        }
      }

      lemma LubDefined_bc(t1_O: Old.validation.types.Type, t2_O: Old.validation.types.Type, t1_N: New.validation.types.Type, t2_N: New.validation.types.Type, m_N: New.validation.types.ValidationMode)
        decreases t1_O, t2_O
        requires t1_N == Type_forward(t1_O)
        requires t2_N == Type_forward(t2_O)
        ensures New.validation.subtyping.LubDefined(t1_N, t2_N, m_N) == Old.validation.subtyping.LubDefined(t1_O, t2_O)
      {
        match Old.validation.subtyping.lubOpt(t1_O, t2_O) {
          case Ok(_) =>
            assert New.validation.subtyping.LubDefined(t1_N, t2_N, m_N) == true;
          case _ =>
            assert New.validation.subtyping.LubDefined(t1_N, t2_N, m_N) == false;
        }
      }

      lemma lub_bc(t1_O: Old.validation.types.Type, t2_O: Old.validation.types.Type, t1_N: New.validation.types.Type, t2_N: New.validation.types.Type, m_N: New.validation.types.ValidationMode)
        decreases t1_O, t2_O
        requires Old.validation.subtyping.LubDefined(t1_O, t2_O)
        requires t1_N == Type_forward(t1_O)
        requires t2_N == Type_forward(t2_O)
        ensures New.validation.subtyping.LubDefined(t1_N, t2_N, m_N)
        ensures New.validation.subtyping.lub(t1_N, t2_N, m_N) == Type_forward(Old.validation.subtyping.lub(t1_O, t2_O))
      {
        match Old.validation.subtyping.lubOpt(t1_O, t2_O) {
          case Ok(t) =>
            assert New.validation.subtyping.lub(t1_N, t2_N, m_N) == Type_forward(t);
        }
      }

      import opened types
    }

    module typechecker {
      import Joint

      import Old

      import New

      import Translations

      import def

      import opened def.core

      import opened types

      import opened ext

      import opened subtyping

      function EntityTypeStore_forward(E_O: Old.validation.typechecker.EntityTypeStore): New.validation.typechecker.EntityTypeStore
      {
        match E_O {
          case EntityTypeStore(types_O, descendants_O) =>
            /* unchanged constructor */ New.validation.typechecker.EntityTypeStore.EntityTypeStore(Translations.MapBuiltinTypes.Map((mp: Joint.def.core.EntityType) => mp, (mp: Joint.def.core.EntityType) => mp, (mp: Old.validation.types.RecordType) => RecordType_forward(mp), types_O), descendants_O)
        }
      }

      function EntityTypeStore_backward(E_N: New.validation.typechecker.EntityTypeStore): Old.validation.typechecker.EntityTypeStore
      {
        match E_N {
          case EntityTypeStore(types_N, descendants_N) =>
            /* unchanged constructor */ Old.validation.typechecker.EntityTypeStore.EntityTypeStore(Translations.MapBuiltinTypes.Map((mp: Joint.def.core.EntityType) => mp, (mp: Joint.def.core.EntityType) => mp, (mp: New.validation.types.RecordType) => RecordType_backward(mp), types_N), descendants_N)
        }
      }

      lemma EntityTypeStore_possibleDescendantOf_bc(E_O: Old.validation.typechecker.EntityTypeStore, E_N: New.validation.typechecker.EntityTypeStore, et1_O: Joint.def.core.EntityType, et2_O: Joint.def.core.EntityType, et1_N: Joint.def.core.EntityType, et2_N: Joint.def.core.EntityType)
        decreases E_O, et1_O, et2_O
        requires E_N == EntityTypeStore_forward(E_O)
        requires et1_N == et1_O
        requires et2_N == et2_O
        ensures E_N.possibleDescendantOf(et1_N, et2_N) == E_O.possibleDescendantOf(et1_O, et2_O)
      {
        if (et1_O == et2_O) {
          assert E_N.possibleDescendantOf(et1_N, et2_N) == true;
        } else {
          if (et2_O in E_O.descendants) {
            assert E_N.possibleDescendantOf(et1_N, et2_N) == (et1_O in E_O.descendants[et2_O]);
          } else {
            assert E_N.possibleDescendantOf(et1_N, et2_N) == false;
          }
        }
      }

      lemma EntityTypeStore_possibleDescendantOfSet_bc(E_O: Old.validation.typechecker.EntityTypeStore, E_N: New.validation.typechecker.EntityTypeStore, et_O: Joint.def.core.EntityType, ets_O: set<Joint.def.core.EntityType>, et_N: Joint.def.core.EntityType, ets_N: set<Joint.def.core.EntityType>)
        decreases E_O, et_O, ets_O
        requires E_N == EntityTypeStore_forward(E_O)
        requires et_N == et_O
        requires ets_N == ets_O
        ensures E_N.possibleDescendantOfSet(et_N, ets_N) == E_O.possibleDescendantOfSet(et_O, ets_O)
      {
        if (exists et1: Joint.def.core.EntityType ::
          et1 in ets_O && (EntityTypeStore_possibleDescendantOf_bc(E_O, E_N, et_O, et1, et_N, et1);
          E_O.possibleDescendantOf(et_O, et1))) {
          var et1 :| et1 in ets_O && (EntityTypeStore_possibleDescendantOf_bc(E_O, E_N, et_O, et1, et_N, et1);
          E_O.possibleDescendantOf(et_O, et1));
          assert E_N.possibleDescendantOf(et_N, et1) by {
            EntityTypeStore_possibleDescendantOf_bc(E_O, E_N, et_O, et1, et_N, et1);
          }
        } else {
          forall et1: Joint.def.core.EntityType | et1 in ets_O
            ensures !E_N.possibleDescendantOf(et_N, et1) {
            EntityTypeStore_possibleDescendantOf_bc(E_O, E_N, et_O, et1, et_N, et1);
          }
        }
      }

      lemma EntityTypeStore_getLubRecordType_bc(E_O: Old.validation.typechecker.EntityTypeStore, E_N: New.validation.typechecker.EntityTypeStore, lub_O: Old.validation.types.EntityLUB, lub_N: New.validation.types.EntityLUB, m_N: New.validation.types.ValidationMode)
        decreases E_O, lub_O
        requires E_N == EntityTypeStore_forward(E_O)
        requires lub_N == EntityLUB_forward(lub_O)
        ensures E_N.getLubRecordType(lub_N, m_N) == Result_forward((x: Old.validation.types.RecordType) => RecordType_forward(x), (x: New.validation.types.RecordType) => RecordType_backward(x), E_O.getLubRecordType(lub_O))
      {
        if (lub_O.AnyEntity? || (exists et: Old.validation.types.EntityType ::
          et in lub_O.tys && (isAction_bc(et, types.EntityType_forward(et));
          Old.validation.types.isAction(et)))) {
          Ok_bc((x: Old.validation.types.RecordType) => RecordType_forward(x), (x: New.validation.types.RecordType) => RecordType_backward(x), Old.validation.types.RecordType.RecordType(map [], Old.validation.types.AttrsTag.OpenAttributes()), New.validation.types.RecordType.RecordType(map [], New.validation.types.AttrsTag.OpenAttributes()));
          assert E_N.getLubRecordType(lub_N, m_N) == Result_forward((x: Old.validation.types.RecordType) => RecordType_forward(x), (x: New.validation.types.RecordType) => RecordType_backward(x), Old.validation.types.Ok(Old.validation.types.RecordType.RecordType(map [], Old.validation.types.AttrsTag.OpenAttributes())));
        } else {
          if (forall et: Joint.def.core.EntityType :: et in lub_O.tys ==> et in E_O.types) {
            Joint.def.util.EntityTypeLeqIsTotalOrder();
            var lubSeq := Joint.def.util.SetToSortedSeq(lub_O.tys, Joint.def.util.EntityTypeLeq); assert E_N.getLubRecordType(lub_N, m_N) == Result_forward((x: Old.validation.types.RecordType) => RecordType_forward(x), (x: New.validation.types.RecordType) => RecordType_backward(x), Old.validation.subtyping.lubRecordTypeSeq(seq(|lubSeq|, (i: int) requires 0 <= i && i < |lubSeq| => E_O.types[lubSeq[i]])));
          } else {
            Err_bc((x: Old.validation.types.RecordType) => RecordType_forward(x), (x: New.validation.types.RecordType) => RecordType_backward(x), Old.validation.types.TypeError.UnknownEntities(set et: Joint.def.core.EntityType | et in lub_O.tys && et !in E_O.types :: et), New.validation.types.TypeError.UnknownEntities(set et: Joint.def.core.EntityType | et in lub_N.tys && et !in E_N.types :: et));
            assert E_N.getLubRecordType(lub_N, m_N) == Result_forward((x: Old.validation.types.RecordType) => RecordType_forward(x), (x: New.validation.types.RecordType) => RecordType_backward(x), Old.validation.types.Err(Old.validation.types.TypeError.UnknownEntities(set et: Joint.def.core.EntityType | et in lub_O.tys && et !in E_O.types :: et)));
          }
        }
      }

      lemma EntityTypeStore_isAttrPossible_bc(E_O: Old.validation.typechecker.EntityTypeStore, E_N: New.validation.typechecker.EntityTypeStore, lub_O: Old.validation.types.EntityLUB, k_O: Joint.def.core.Attr, lub_N: New.validation.types.EntityLUB, k_N: Joint.def.core.Attr)
        decreases E_O, lub_O, k_O
        requires E_N == EntityTypeStore_forward(E_O)
        requires lub_N == EntityLUB_forward(lub_O)
        requires k_N == k_O
        ensures E_N.isAttrPossible(lub_N, k_N) == E_O.isAttrPossible(lub_O, k_O)
      {
        assert E_N.isAttrPossible(lub_N, k_N) == (lub_O.AnyEntity? || (exists e: Joint.def.core.EntityType ::
          e in lub_O.tys && (e in E_O.types && ((RecordType_isOpen_bc(E_O.types[e], E_N.types[e]);
          E_O.types[e].isOpen()) || k_O in E_O.types[e].attrs))));
      }

      function ActionStore_forward(A_O: Old.validation.typechecker.ActionStore): New.validation.typechecker.ActionStore
      {
        match A_O {
          case ActionStore(descendants_O) =>
            /* unchanged constructor */ New.validation.typechecker.ActionStore.ActionStore(descendants_O)
        }
      }

      function ActionStore_backward(A_N: New.validation.typechecker.ActionStore): Old.validation.typechecker.ActionStore
      {
        match A_N {
          case ActionStore(descendants_N) =>
            /* unchanged constructor */ Old.validation.typechecker.ActionStore.ActionStore(descendants_N)
        }
      }

      lemma {:axiom} ActionStore_descendantOf_bc(A_O: Old.validation.typechecker.ActionStore, A_N: New.validation.typechecker.ActionStore, euid1_O: Joint.def.core.EntityUID, euid2_O: Joint.def.core.EntityUID, euid1_N: Joint.def.core.EntityUID, euid2_N: Joint.def.core.EntityUID)
        decreases A_O, euid1_O, euid2_O
        requires A_N == ActionStore_forward(A_O)
        requires euid1_N == euid1_O
        requires euid2_N == euid2_O
        ensures A_N.descendantOf(euid1_N, euid2_N) == A_O.descendantOf(euid1_O, euid2_O)

      lemma {:axiom} ActionStore_descendantOfSet_bc(A_O: Old.validation.typechecker.ActionStore, A_N: New.validation.typechecker.ActionStore, euid_O: Joint.def.core.EntityUID, euids_O: set<Joint.def.core.EntityUID>, euid_N: Joint.def.core.EntityUID, euids_N: set<Joint.def.core.EntityUID>)
        decreases A_O, euid_O, euids_O
        requires A_N == ActionStore_forward(A_O)
        requires euid_N == euid_O
        requires euids_N == euids_O
        ensures A_N.descendantOfSet(euid_N, euids_N) == A_O.descendantOfSet(euid_O, euids_O)

      function RequestType_forward(R_O: Old.validation.typechecker.RequestType): New.validation.typechecker.RequestType
      {
        match R_O {
          case RequestType(principal_O, action_O, resource_O, context_O) =>
            /* unchanged constructor */ New.validation.typechecker.RequestType.RequestType(Option_forward((x: Joint.def.core.EntityType) => x, (x: Joint.def.core.EntityType) => x, principal_O), action_O, Option_forward((x: Joint.def.core.EntityType) => x, (x: Joint.def.core.EntityType) => x, resource_O), RecordType_forward(context_O))
        }
      }

      function RequestType_backward(R_N: New.validation.typechecker.RequestType): Old.validation.typechecker.RequestType
      {
        match R_N {
          case RequestType(principal_N, action_N, resource_N, context_N) =>
            /* unchanged constructor */ Old.validation.typechecker.RequestType.RequestType(Option_backward((x: Joint.def.core.EntityType) => x, (x: Joint.def.core.EntityType) => x, principal_N), action_N, Option_backward((x: Joint.def.core.EntityType) => x, (x: Joint.def.core.EntityType) => x, resource_N), RecordType_backward(context_N))
        }
      }

      function Effects_forward(E_O: Old.validation.typechecker.Effects): New.validation.typechecker.Effects
      {
        match E_O {
          case Effects(effs_O) =>
            /* unchanged constructor */ New.validation.typechecker.Effects.Effects(effs_O)
        }
      }

      function Effects_backward(E_N: New.validation.typechecker.Effects): Old.validation.typechecker.Effects
      {
        match E_N {
          case Effects(effs_N) =>
            /* unchanged constructor */ Old.validation.typechecker.Effects.Effects(effs_N)
        }
      }

      lemma {:axiom} Effects_union_bc(E_O: Old.validation.typechecker.Effects, E_N: New.validation.typechecker.Effects, other_O: Old.validation.typechecker.Effects, other_N: New.validation.typechecker.Effects)
        decreases E_O, other_O
        requires E_N == Effects_forward(E_O)
        requires other_N == Effects_forward(other_O)
        ensures E_N.union(other_N) == Effects_forward(E_O.union(other_O))

      lemma {:axiom} Effects_intersect_bc(E_O: Old.validation.typechecker.Effects, E_N: New.validation.typechecker.Effects, other_O: Old.validation.typechecker.Effects, other_N: New.validation.typechecker.Effects)
        decreases E_O, other_O
        requires E_N == Effects_forward(E_O)
        requires other_N == Effects_forward(other_O)
        ensures E_N.intersect(other_N) == Effects_forward(E_O.intersect(other_O))

      lemma {:axiom} Effects_contains_bc(E_O: Old.validation.typechecker.Effects, E_N: New.validation.typechecker.Effects, e_O: Joint.def.core.Expr, a_O: Joint.def.core.Attr, e_N: Joint.def.core.Expr, a_N: Joint.def.core.Attr)
        decreases E_O, e_O, a_O
        requires E_N == Effects_forward(E_O)
        requires e_N == e_O
        requires a_N == a_O
        ensures E_N.contains(e_N, a_N) == E_O.contains(e_O, a_O)

      lemma {:axiom} Effects_empty_bc()
        ensures New.validation.typechecker.Effects.empty() == Effects_forward(Old.validation.typechecker.Effects.empty())

      lemma {:axiom} Effects_singleton_bc(e_O: Joint.def.core.Expr, a_O: Joint.def.core.Attr, e_N: Joint.def.core.Expr, a_N: Joint.def.core.Attr)
        decreases e_O, a_O
        requires e_N == e_O
        requires a_N == a_O
        ensures New.validation.typechecker.Effects.singleton(e_N, a_N) == Effects_forward(Old.validation.typechecker.Effects.singleton(e_O, a_O))

      function Typechecker_forward(T_O: Old.validation.typechecker.Typechecker): New.validation.typechecker.Typechecker
      {
        match T_O {
          case Typechecker(ets_O, acts_O, reqty_O) =>
            /* added/deleted/updated constructor arguments */ New.validation.typechecker.Typechecker.Typechecker(EntityTypeStore_forward(ets_O), ActionStore_forward(acts_O), RequestType_forward(reqty_O), Translations.Utils.???())
        }
      }

      function Typechecker_backward(T_N: New.validation.typechecker.Typechecker): Old.validation.typechecker.Typechecker
      {
        match T_N {
          case Typechecker(ets_N, acts_N, reqty_N, mode_N) =>
            /* added/deleted/updated constructor arguments */ Old.validation.typechecker.Typechecker.Typechecker(EntityTypeStore_backward(ets_N), ActionStore_backward(acts_N), RequestType_backward(reqty_N))
        }
      }

      lemma Typechecker_ensureSubty_bc(T_O: Old.validation.typechecker.Typechecker, T_N: New.validation.typechecker.Typechecker, t1_O: Old.validation.types.Type, t2_O: Old.validation.types.Type, t1_N: New.validation.types.Type, t2_N: New.validation.types.Type)
        decreases T_O, t1_O, t2_O
        requires T_N == Typechecker_forward(T_O)
        requires t1_N == Type_forward(t1_O)
        requires t2_N == Type_forward(t2_O)
        ensures T_N.ensureSubty(t1_N, t2_N) == Result_forward((x: ()) => (), (x: ()) => (), T_O.ensureSubty(t1_O, t2_O))
      {
        if (Old.validation.subtyping.subty(t1_O, t2_O)) {
          Ok_bc((x: ()) => (), (x: ()) => (), (), ());
          assert T_N.ensureSubty(t1_N, t2_N) == Result_forward((x: ()) => (), (x: ()) => (), Old.validation.types.Ok(()));
        } else {
          Err_bc((x: ()) => (), (x: ()) => (), Old.validation.types.TypeError.SubtyErr(t1_O, t2_O), New.validation.types.TypeError.SubtyErr(t1_N, t2_N));
          assert T_N.ensureSubty(t1_N, t2_N) == Result_forward((x: ()) => (), (x: ()) => (), Old.validation.types.Err(Old.validation.types.TypeError.SubtyErr(t1_O, t2_O)));
        }
      }

      lemma Typechecker_ensureStringType_bc(T_O: Old.validation.typechecker.Typechecker, T_N: New.validation.typechecker.Typechecker, e_O: Joint.def.core.Expr, effs_O: Old.validation.typechecker.Effects, e_N: Joint.def.core.Expr, effs_N: New.validation.typechecker.Effects)
        decreases e_O, 2
        requires T_N == Typechecker_forward(T_O)
        requires e_N == e_O
        requires effs_N == Effects_forward(effs_O)
        ensures T_N.ensureStringType(e_N, effs_N) == Result_forward((x: ()) => (), (x: ()) => (), T_O.ensureStringType(e_O, effs_O))
      {
        assert T_N.ensureStringType(e_N, effs_N) == Result_forward((x: ()) => (), (x: ()) => (), var (t, _) :- (Typechecker_infer_bc(T_O, T_N, e_O, effs_O, e_N, effs_N);
        T_O.infer(e_O, effs_O));
        match t {
          case String() =>
            Ok_bc((x: ()) => (), (x: ()) => (), (), ());
            Old.validation.types.Ok(())
          case _ =>
            Err_bc((x: ()) => (), (x: ()) => (), Old.validation.types.TypeError.UnexpectedType(t), New.validation.types.TypeError.UnexpectedType(Type_forward(t)));
            Old.validation.types.Err(Old.validation.types.TypeError.UnexpectedType(t))
        });
      }

      lemma Typechecker_ensureIntType_bc(T_O: Old.validation.typechecker.Typechecker, T_N: New.validation.typechecker.Typechecker, e_O: Joint.def.core.Expr, effs_O: Old.validation.typechecker.Effects, e_N: Joint.def.core.Expr, effs_N: New.validation.typechecker.Effects)
        decreases e_O, 2
        requires T_N == Typechecker_forward(T_O)
        requires e_N == e_O
        requires effs_N == Effects_forward(effs_O)
        ensures T_N.ensureIntType(e_N, effs_N) == Result_forward((x: ()) => (), (x: ()) => (), T_O.ensureIntType(e_O, effs_O))
      {
        assert T_N.ensureIntType(e_N, effs_N) == Result_forward((x: ()) => (), (x: ()) => (), var (t, _) :- (Typechecker_infer_bc(T_O, T_N, e_O, effs_O, e_N, effs_N);
        T_O.infer(e_O, effs_O));
        match t {
          case Int() =>
            Ok_bc((x: ()) => (), (x: ()) => (), (), ());
            Old.validation.types.Ok(())
          case _ =>
            Err_bc((x: ()) => (), (x: ()) => (), Old.validation.types.TypeError.UnexpectedType(t), New.validation.types.TypeError.UnexpectedType(Type_forward(t)));
            Old.validation.types.Err(Old.validation.types.TypeError.UnexpectedType(t))
        });
      }

      lemma Typechecker_ensureEntityType_bc(T_O: Old.validation.typechecker.Typechecker, T_N: New.validation.typechecker.Typechecker, e_O: Joint.def.core.Expr, effs_O: Old.validation.typechecker.Effects, e_N: Joint.def.core.Expr, effs_N: New.validation.typechecker.Effects)
        decreases e_O, 2
        requires T_N == Typechecker_forward(T_O)
        requires e_N == e_O
        requires effs_N == Effects_forward(effs_O)
        ensures /* cannot translate output type */ false
      {}

      lemma Typechecker_ensureEntitySetType_bc(T_O: Old.validation.typechecker.Typechecker, T_N: New.validation.typechecker.Typechecker, e_O: Joint.def.core.Expr, effs_O: Old.validation.typechecker.Effects, e_N: Joint.def.core.Expr, effs_N: New.validation.typechecker.Effects)
        decreases e_O, 2
        requires T_N == Typechecker_forward(T_O)
        requires e_N == e_O
        requires effs_N == Effects_forward(effs_O)
        ensures /* cannot translate output type */ false
      {}

      lemma Typechecker_inferPrim_bc(T_O: Old.validation.typechecker.Typechecker, T_N: New.validation.typechecker.Typechecker, p_O: Joint.def.core.Primitive, p_N: Joint.def.core.Primitive)
        decreases T_O, p_O
        requires T_N == Typechecker_forward(T_O)
        requires p_N == p_O
        ensures T_N.inferPrim(p_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), T_O.inferPrim(p_O))
      {
        match p_O {
          case Bool(true) =>
            Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Bool(Old.validation.types.BoolType.True()), New.validation.types.Type.Bool(New.validation.types.BoolType.True()));
            assert T_N.inferPrim(p_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Ok(Old.validation.types.Type.Bool(Old.validation.types.BoolType.True())));
          case Bool(false) =>
            Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Bool(Old.validation.types.BoolType.False()), New.validation.types.Type.Bool(New.validation.types.BoolType.False()));
            assert T_N.inferPrim(p_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Ok(Old.validation.types.Type.Bool(Old.validation.types.BoolType.False())));
          case Int(_) =>
            Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Int(), New.validation.types.Type.Int());
            assert T_N.inferPrim(p_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Ok(Old.validation.types.Type.Int()));
          case String(_) =>
            Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.String(), New.validation.types.Type.String());
            assert T_N.inferPrim(p_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Ok(Old.validation.types.Type.String()));
          case EntityUID(u) =>
            if (u.ty in T_O.ets.types || (isAction_bc(u.ty, u.ty);
            Old.validation.types.isAction(u.ty))) {
              Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Entity(Old.validation.types.EntityLUB.EntityLUB({u.ty})), New.validation.types.Type.Entity(New.validation.types.EntityLUB.EntityLUB({u.ty})));
              assert T_N.inferPrim(p_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Ok(Old.validation.types.Type.Entity(Old.validation.types.EntityLUB.EntityLUB({u.ty}))));
            } else {
              Err_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.TypeError.UnknownEntities({u.ty}), New.validation.types.TypeError.UnknownEntities({u.ty}));
              assert T_N.inferPrim(p_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Err(Old.validation.types.TypeError.UnknownEntities({u.ty})));
            }
        }
      }

      lemma Typechecker_inferVar_bc(T_O: Old.validation.typechecker.Typechecker, T_N: New.validation.typechecker.Typechecker, x_O: Joint.def.core.Var, x_N: Joint.def.core.Var)
        decreases T_O, x_O
        requires T_N == Typechecker_forward(T_O)
        requires x_N == x_O
        ensures T_N.inferVar(x_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), T_O.inferVar(x_O))
      {
        match x_O {
          case Principal() =>
            if (T_O.reqty.principal.None?) {
              Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Entity(Old.validation.types.EntityLUB.AnyEntity()), New.validation.types.Type.Entity(New.validation.types.EntityLUB.AnyEntity()));
              assert T_N.inferVar(x_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Ok(Old.validation.types.Type.Entity(Old.validation.types.EntityLUB.AnyEntity())));
            } else {
              Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Entity(Old.validation.types.EntityLUB.EntityLUB({T_O.reqty.principal.value})), New.validation.types.Type.Entity(New.validation.types.EntityLUB.EntityLUB({T_N.reqty.principal.value})));
              assert T_N.inferVar(x_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Ok(Old.validation.types.Type.Entity(Old.validation.types.EntityLUB.EntityLUB({T_O.reqty.principal.value}))));
            }
          case Context() =>
            Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Record(T_O.reqty.context), New.validation.types.Type.Record(T_N.reqty.context));
            assert T_N.inferVar(x_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Ok(Old.validation.types.Type.Record(T_O.reqty.context)));
          case Action() =>
            Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Entity(Old.validation.types.EntityLUB.EntityLUB({T_O.reqty.action.ty})), New.validation.types.Type.Entity(New.validation.types.EntityLUB.EntityLUB({T_N.reqty.action.ty})));
            assert T_N.inferVar(x_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Ok(Old.validation.types.Type.Entity(Old.validation.types.EntityLUB.EntityLUB({T_O.reqty.action.ty}))));
          case Resource() =>
            if (T_O.reqty.resource.None?) {
              Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Entity(Old.validation.types.EntityLUB.AnyEntity()), New.validation.types.Type.Entity(New.validation.types.EntityLUB.AnyEntity()));
              assert T_N.inferVar(x_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Ok(Old.validation.types.Type.Entity(Old.validation.types.EntityLUB.AnyEntity())));
            } else {
              Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Entity(Old.validation.types.EntityLUB.EntityLUB({T_O.reqty.resource.value})), New.validation.types.Type.Entity(New.validation.types.EntityLUB.EntityLUB({T_N.reqty.resource.value})));
              assert T_N.inferVar(x_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Ok(Old.validation.types.Type.Entity(Old.validation.types.EntityLUB.EntityLUB({T_O.reqty.resource.value}))));
            }
        }
      }

      lemma Typechecker_inferBoolType_bc(T_O: Old.validation.typechecker.Typechecker, T_N: New.validation.typechecker.Typechecker, e_O: Joint.def.core.Expr, effs_O: Old.validation.typechecker.Effects, e_N: Joint.def.core.Expr, effs_N: New.validation.typechecker.Effects)
        decreases e_O, 2
        requires T_N == Typechecker_forward(T_O)
        requires e_N == e_O
        requires effs_N == Effects_forward(effs_O)
        ensures T_N.inferBoolType(e_N, effs_N) == Result_forward((x: (Old.validation.types.BoolType,Old.validation.typechecker.Effects)) => (BoolType_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.BoolType,New.validation.typechecker.Effects)) => (BoolType_backward(x.0), Effects_backward(x.1)), T_O.inferBoolType(e_O, effs_O))
      {
        assert T_N.inferBoolType(e_N, effs_N) == Result_forward((x: (Old.validation.types.BoolType,Old.validation.typechecker.Effects)) => (BoolType_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.BoolType,New.validation.typechecker.Effects)) => (BoolType_backward(x.0), Effects_backward(x.1)), var (t, effs1) :- (Typechecker_infer_bc(T_O, T_N, e_O, effs_O, e_N, effs_N);
        T_O.infer(e_O, effs_O));
        match t {
          case Bool(bt) =>
            Ok_bc((x: (Old.validation.types.BoolType,Old.validation.typechecker.Effects)) => (BoolType_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.BoolType,New.validation.typechecker.Effects)) => (BoolType_backward(x.0), Effects_backward(x.1)), (bt, effs1), (BoolType_forward(bt), Effects_forward(effs1)));
            Old.validation.types.Ok((bt, effs1))
          case _ =>
            Err_bc((x: (Old.validation.types.BoolType,Old.validation.typechecker.Effects)) => (BoolType_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.BoolType,New.validation.typechecker.Effects)) => (BoolType_backward(x.0), Effects_backward(x.1)), Old.validation.types.TypeError.UnexpectedType(t), New.validation.types.TypeError.UnexpectedType(Type_forward(t)));
            Old.validation.types.Err(Old.validation.types.TypeError.UnexpectedType(t))
        });
      }

      lemma Typechecker_inferSetType_bc(T_O: Old.validation.typechecker.Typechecker, T_N: New.validation.typechecker.Typechecker, e_O: Joint.def.core.Expr, effs_O: Old.validation.typechecker.Effects, e_N: Joint.def.core.Expr, effs_N: New.validation.typechecker.Effects)
        decreases e_O, 2
        requires T_N == Typechecker_forward(T_O)
        requires e_N == e_O
        requires effs_N == Effects_forward(effs_O)
        ensures T_N.inferSetType(e_N, effs_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), T_O.inferSetType(e_O, effs_O))
      {
        assert T_N.inferSetType(e_N, effs_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), var (t, _) :- (Typechecker_infer_bc(T_O, T_N, e_O, effs_O, e_N, effs_N);
        T_O.infer(e_O, effs_O));
        match t {
          case Set(t1) =>
            Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), t1, Type_forward(t1));
            Old.validation.types.Ok(t1)
          case _ =>
            Err_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.TypeError.UnexpectedType(t), New.validation.types.TypeError.UnexpectedType(Type_forward(t)));
            Old.validation.types.Err(Old.validation.types.TypeError.UnexpectedType(t))
        });
      }

      lemma Typechecker_inferRecordEntityType_bc(T_O: Old.validation.typechecker.Typechecker, T_N: New.validation.typechecker.Typechecker, e_O: Joint.def.core.Expr, effs_O: Old.validation.typechecker.Effects, e_N: Joint.def.core.Expr, effs_N: New.validation.typechecker.Effects)
        decreases e_O, 2
        requires T_N == Typechecker_forward(T_O)
        requires e_N == e_O
        requires effs_N == Effects_forward(effs_O)
        ensures T_N.inferRecordEntityType(e_N, effs_N) == Result_forward((x: Old.validation.types.RecordEntityType) => RecordEntityType_forward(x), (x: New.validation.types.RecordEntityType) => RecordEntityType_backward(x), T_O.inferRecordEntityType(e_O, effs_O))
      {
        assert T_N.inferRecordEntityType(e_N, effs_N) == Result_forward((x: Old.validation.types.RecordEntityType) => RecordEntityType_forward(x), (x: New.validation.types.RecordEntityType) => RecordEntityType_backward(x), var (t, _) :- (Typechecker_infer_bc(T_O, T_N, e_O, effs_O, e_N, effs_N);
        T_O.infer(e_O, effs_O));
        match t {
          case Record(rt) =>
            Ok_bc((x: Old.validation.types.RecordEntityType) => RecordEntityType_forward(x), (x: New.validation.types.RecordEntityType) => RecordEntityType_backward(x), Old.validation.types.RecordEntityType.Record(rt), New.validation.types.RecordEntityType.Record(RecordType_forward(rt)));
            Old.validation.types.Ok(Old.validation.types.RecordEntityType.Record(rt))
          case Entity(lub) =>
            Ok_bc((x: Old.validation.types.RecordEntityType) => RecordEntityType_forward(x), (x: New.validation.types.RecordEntityType) => RecordEntityType_backward(x), Old.validation.types.RecordEntityType.Entity(lub), New.validation.types.RecordEntityType.Entity(EntityLUB_forward(lub)));
            Old.validation.types.Ok(Old.validation.types.RecordEntityType.Entity(lub))
          case _ =>
            Err_bc((x: Old.validation.types.RecordEntityType) => RecordEntityType_forward(x), (x: New.validation.types.RecordEntityType) => RecordEntityType_backward(x), Old.validation.types.TypeError.UnexpectedType(t), New.validation.types.TypeError.UnexpectedType(Type_forward(t)));
            Old.validation.types.Err(Old.validation.types.TypeError.UnexpectedType(t))
        });
      }

      lemma Typechecker_inferIf_bc(T_O: Old.validation.typechecker.Typechecker, T_N: New.validation.typechecker.Typechecker, e1_O: Joint.def.core.Expr, e2_O: Joint.def.core.Expr, e3_O: Joint.def.core.Expr, effs_O: Old.validation.typechecker.Effects, e1_N: Joint.def.core.Expr, e2_N: Joint.def.core.Expr, e3_N: Joint.def.core.Expr, effs_N: New.validation.typechecker.Effects)
        decreases Joint.def.core.Expr.If(e1_O, e2_O, e3_O), 0
        requires T_N == Typechecker_forward(T_O)
        requires e1_N == e1_O
        requires e2_N == e2_O
        requires e3_N == e3_O
        requires effs_N == Effects_forward(effs_O)
        ensures T_N.inferIf(e1_N, e2_N, e3_N, effs_N) == Result_forward((x: (Old.validation.types.Type,Old.validation.typechecker.Effects)) => (Type_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.Type,New.validation.typechecker.Effects)) => (Type_backward(x.0), Effects_backward(x.1)), T_O.inferIf(e1_O, e2_O, e3_O, effs_O))
      {
        assert T_N.inferIf(e1_N, e2_N, e3_N, effs_N) == Result_forward((x: (Old.validation.types.Type,Old.validation.typechecker.Effects)) => (Type_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.Type,New.validation.typechecker.Effects)) => (Type_backward(x.0), Effects_backward(x.1)), var (bt, effs1) :- (Typechecker_inferBoolType_bc(T_O, T_N, e1_O, effs_O, e1_N, effs_N);
        T_O.inferBoolType(e1_O, effs_O));
        match bt {
          case True() =>
            var (t, effs2) :- (Typechecker_infer_bc(T_O, T_N, e2_O, effs_O.union(effs1), e2_N, effs_N.union(Effects_forward(effs1)));
            T_O.infer(e2_O, Effects_union_bc(effs_O, effs_N, effs1, Effects_forward(effs1));
            effs_O.union(effs1)));
            Ok_bc((x: (Old.validation.types.Type,Old.validation.typechecker.Effects)) => (Type_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.Type,New.validation.typechecker.Effects)) => (Type_backward(x.0), Effects_backward(x.1)), (t, effs1.union(effs2)), (Type_forward(t), Effects_forward(effs1).union(Effects_forward(effs2))));
            Old.validation.types.Ok((t, Effects_union_bc(effs1, Effects_forward(effs1), effs2, Effects_forward(effs2));
            effs1.union(effs2)))
          case False() =>
            Typechecker_infer_bc(T_O, T_N, e3_O, effs_O, e3_N, effs_N);
            T_O.infer(e3_O, effs_O)
          case Bool =>
            var (t1, effs2) :- (Typechecker_infer_bc(T_O, T_N, e2_O, effs_O.union(effs1), e2_N, effs_N.union(Effects_forward(effs1)));
            T_O.infer(e2_O, Effects_union_bc(effs_O, effs_N, effs1, Effects_forward(effs1));
            effs_O.union(effs1)));
            var (t2, effs3) :- (Typechecker_infer_bc(T_O, T_N, e3_O, effs_O, e3_N, effs_N);
            T_O.infer(e3_O, effs_O));
            var t :- Old.validation.subtyping.lubOpt(t1, t2);
            Ok_bc((x: (Old.validation.types.Type,Old.validation.typechecker.Effects)) => (Type_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.Type,New.validation.typechecker.Effects)) => (Type_backward(x.0), Effects_backward(x.1)), (t, effs1.union(effs2).intersect(effs3)), (Type_forward(t), Effects_forward(effs1).union(Effects_forward(effs2)).intersect(Effects_forward(effs3))));
            Old.validation.types.Ok((t, Effects_intersect_bc(effs1.union(effs2), Effects_forward(effs1).union(Effects_forward(effs2)), effs3, Effects_forward(effs3));
            (Effects_union_bc(effs1, Effects_forward(effs1), effs2, Effects_forward(effs2));
            effs1.union(effs2)).intersect(effs3)))
        });
      }

      lemma Typechecker_inferAnd_bc(T_O: Old.validation.typechecker.Typechecker, T_N: New.validation.typechecker.Typechecker, e1_O: Joint.def.core.Expr, e2_O: Joint.def.core.Expr, effs_O: Old.validation.typechecker.Effects, e1_N: Joint.def.core.Expr, e2_N: Joint.def.core.Expr, effs_N: New.validation.typechecker.Effects)
        decreases Joint.def.core.Expr.And(e1_O, e2_O), 0
        requires T_N == Typechecker_forward(T_O)
        requires e1_N == e1_O
        requires e2_N == e2_O
        requires effs_N == Effects_forward(effs_O)
        ensures T_N.inferAnd(e1_N, e2_N, effs_N) == Result_forward((x: (Old.validation.types.Type,Old.validation.typechecker.Effects)) => (Type_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.Type,New.validation.typechecker.Effects)) => (Type_backward(x.0), Effects_backward(x.1)), T_O.inferAnd(e1_O, e2_O, effs_O))
      {
        assert T_N.inferAnd(e1_N, e2_N, effs_N) == Result_forward((x: (Old.validation.types.Type,Old.validation.typechecker.Effects)) => (Type_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.Type,New.validation.typechecker.Effects)) => (Type_backward(x.0), Effects_backward(x.1)), var (bt1, effs1) :- (Typechecker_inferBoolType_bc(T_O, T_N, e1_O, effs_O, e1_N, effs_N);
        T_O.inferBoolType(e1_O, effs_O));
        match bt1 {
          case False() =>
            Typechecker_wrap_bc(T_O, T_N, Old.validation.types.Ok(Old.validation.types.Type.Bool(Old.validation.types.BoolType.False())), New.validation.types.Ok(New.validation.types.Type.Bool(New.validation.types.BoolType.False())));
            T_O.wrap(Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Bool(Old.validation.types.BoolType.False()), New.validation.types.Type.Bool(New.validation.types.BoolType.False()));
            Old.validation.types.Ok(Old.validation.types.Type.Bool(Old.validation.types.BoolType.False())))
          case _ =>
            var (bt2, effs2) :- (Typechecker_inferBoolType_bc(T_O, T_N, e2_O, effs_O.union(effs1), e2_N, effs_N.union(Effects_forward(effs1)));
            T_O.inferBoolType(e2_O, Effects_union_bc(effs_O, effs_N, effs1, Effects_forward(effs1));
            effs_O.union(effs1)));
            match bt2 {
              case False() =>
                Typechecker_wrap_bc(T_O, T_N, Old.validation.types.Ok(Old.validation.types.Type.Bool(Old.validation.types.BoolType.False())), New.validation.types.Ok(New.validation.types.Type.Bool(New.validation.types.BoolType.False())));
                T_O.wrap(Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Bool(Old.validation.types.BoolType.False()), New.validation.types.Type.Bool(New.validation.types.BoolType.False()));
                Old.validation.types.Ok(Old.validation.types.Type.Bool(Old.validation.types.BoolType.False())))
              case True() =>
                Ok_bc((x: (Old.validation.types.Type,Old.validation.typechecker.Effects)) => (Type_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.Type,New.validation.typechecker.Effects)) => (Type_backward(x.0), Effects_backward(x.1)), (Old.validation.types.Type.Bool(bt1), effs1.union(effs2)), (New.validation.types.Type.Bool(BoolType_forward(bt1)), Effects_forward(effs1).union(Effects_forward(effs2))));
                Old.validation.types.Ok((Old.validation.types.Type.Bool(bt1), Effects_union_bc(effs1, Effects_forward(effs1), effs2, Effects_forward(effs2));
                effs1.union(effs2)))
              case _ =>
                Ok_bc((x: (Old.validation.types.Type,Old.validation.typechecker.Effects)) => (Type_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.Type,New.validation.typechecker.Effects)) => (Type_backward(x.0), Effects_backward(x.1)), (Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool()), effs1.union(effs2)), (New.validation.types.Type.Bool(New.validation.types.BoolType.AnyBool()), Effects_forward(effs1).union(Effects_forward(effs2))));
                Old.validation.types.Ok((Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool()), Effects_union_bc(effs1, Effects_forward(effs1), effs2, Effects_forward(effs2));
                effs1.union(effs2)))
            }
        });
      }

      lemma Typechecker_inferOr_bc(T_O: Old.validation.typechecker.Typechecker, T_N: New.validation.typechecker.Typechecker, e1_O: Joint.def.core.Expr, e2_O: Joint.def.core.Expr, effs_O: Old.validation.typechecker.Effects, e1_N: Joint.def.core.Expr, e2_N: Joint.def.core.Expr, effs_N: New.validation.typechecker.Effects)
        decreases Joint.def.core.Expr.Or(e1_O, e2_O), 0
        requires T_N == Typechecker_forward(T_O)
        requires e1_N == e1_O
        requires e2_N == e2_O
        requires effs_N == Effects_forward(effs_O)
        ensures T_N.inferOr(e1_N, e2_N, effs_N) == Result_forward((x: (Old.validation.types.Type,Old.validation.typechecker.Effects)) => (Type_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.Type,New.validation.typechecker.Effects)) => (Type_backward(x.0), Effects_backward(x.1)), T_O.inferOr(e1_O, e2_O, effs_O))
      {
        assert T_N.inferOr(e1_N, e2_N, effs_N) == Result_forward((x: (Old.validation.types.Type,Old.validation.typechecker.Effects)) => (Type_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.Type,New.validation.typechecker.Effects)) => (Type_backward(x.0), Effects_backward(x.1)), var (bt1, effs1) :- (Typechecker_inferBoolType_bc(T_O, T_N, e1_O, effs_O, e1_N, effs_N);
        T_O.inferBoolType(e1_O, effs_O));
        match bt1 {
          case True() =>
            Typechecker_wrap_bc(T_O, T_N, Old.validation.types.Ok(Old.validation.types.Type.Bool(Old.validation.types.BoolType.True())), New.validation.types.Ok(New.validation.types.Type.Bool(New.validation.types.BoolType.True())));
            T_O.wrap(Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Bool(Old.validation.types.BoolType.True()), New.validation.types.Type.Bool(New.validation.types.BoolType.True()));
            Old.validation.types.Ok(Old.validation.types.Type.Bool(Old.validation.types.BoolType.True())))
          case False() =>
            var (bt2, effs2) :- (Typechecker_inferBoolType_bc(T_O, T_N, e2_O, effs_O, e2_N, effs_N);
            T_O.inferBoolType(e2_O, effs_O));
            Ok_bc((x: (Old.validation.types.Type,Old.validation.typechecker.Effects)) => (Type_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.Type,New.validation.typechecker.Effects)) => (Type_backward(x.0), Effects_backward(x.1)), (Old.validation.types.Type.Bool(bt2), effs2), (New.validation.types.Type.Bool(BoolType_forward(bt2)), Effects_forward(effs2)));
            Old.validation.types.Ok((Old.validation.types.Type.Bool(bt2), effs2))
          case _ =>
            var (bt2, effs2) :- (Typechecker_inferBoolType_bc(T_O, T_N, e2_O, effs_O, e2_N, effs_N);
            T_O.inferBoolType(e2_O, effs_O));
            match bt2 {
              case True() =>
                Typechecker_wrap_bc(T_O, T_N, Old.validation.types.Ok(Old.validation.types.Type.Bool(Old.validation.types.BoolType.True())), New.validation.types.Ok(New.validation.types.Type.Bool(New.validation.types.BoolType.True())));
                T_O.wrap(Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Bool(Old.validation.types.BoolType.True()), New.validation.types.Type.Bool(New.validation.types.BoolType.True()));
                Old.validation.types.Ok(Old.validation.types.Type.Bool(Old.validation.types.BoolType.True())))
              case False() =>
                Ok_bc((x: (Old.validation.types.Type,Old.validation.typechecker.Effects)) => (Type_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.Type,New.validation.typechecker.Effects)) => (Type_backward(x.0), Effects_backward(x.1)), (Old.validation.types.Type.Bool(bt1), effs1), (New.validation.types.Type.Bool(BoolType_forward(bt1)), Effects_forward(effs1)));
                Old.validation.types.Ok((Old.validation.types.Type.Bool(bt1), effs1))
              case _ =>
                Ok_bc((x: (Old.validation.types.Type,Old.validation.typechecker.Effects)) => (Type_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.Type,New.validation.typechecker.Effects)) => (Type_backward(x.0), Effects_backward(x.1)), (Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool()), effs1.intersect(effs2)), (New.validation.types.Type.Bool(New.validation.types.BoolType.AnyBool()), Effects_forward(effs1).intersect(Effects_forward(effs2))));
                Old.validation.types.Ok((Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool()), Effects_intersect_bc(effs1, Effects_forward(effs1), effs2, Effects_forward(effs2));
                effs1.intersect(effs2)))
            }
        });
      }

      lemma Typechecker_inferNot_bc(T_O: Old.validation.typechecker.Typechecker, T_N: New.validation.typechecker.Typechecker, e_O: Joint.def.core.Expr, effs_O: Old.validation.typechecker.Effects, e_N: Joint.def.core.Expr, effs_N: New.validation.typechecker.Effects)
        decreases Joint.def.core.Expr.UnaryApp(Joint.def.core.UnaryOp.Not(), e_O), 0
        requires T_N == Typechecker_forward(T_O)
        requires e_N == e_O
        requires effs_N == Effects_forward(effs_O)
        ensures T_N.inferNot(e_N, effs_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), T_O.inferNot(e_O, effs_O))
      {
        assert T_N.inferNot(e_N, effs_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), var (bt, _) :- (Typechecker_inferBoolType_bc(T_O, T_N, e_O, effs_O, e_N, effs_N);
        T_O.inferBoolType(e_O, effs_O));
        Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Bool(bt.not()), New.validation.types.Type.Bool(BoolType_forward(bt).not()));
        Old.validation.types.Ok(Old.validation.types.Type.Bool(BoolType_not_bc(bt, BoolType_forward(bt));
        bt.not())));
      }

      lemma Typechecker_inferEq_bc(T_O: Old.validation.typechecker.Typechecker, T_N: New.validation.typechecker.Typechecker, e1_O: Joint.def.core.Expr, e2_O: Joint.def.core.Expr, effs_O: Old.validation.typechecker.Effects, e1_N: Joint.def.core.Expr, e2_N: Joint.def.core.Expr, effs_N: New.validation.typechecker.Effects)
        decreases Joint.def.core.Expr.BinaryApp(Joint.def.core.BinaryOp.Eq(), e1_O, e2_O), 0
        requires T_N == Typechecker_forward(T_O)
        requires e1_N == e1_O
        requires e2_N == e2_O
        requires effs_N == Effects_forward(effs_O)
        ensures T_N.inferEq(e1_N, e2_N, effs_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), T_O.inferEq(e1_O, e2_O, effs_O))
      {
        assert T_N.inferEq(e1_N, e2_N, effs_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), var (t1, _) :- (Typechecker_infer_bc(T_O, T_N, e1_O, effs_O, e1_N, effs_N);
        T_O.infer(e1_O, effs_O));
        var (t2, _) :- (Typechecker_infer_bc(T_O, T_N, e2_O, effs_O, e2_N, effs_N);
        T_O.infer(e2_O, effs_O));
        if t1.Entity? && t2.Entity? && (EntityLUB_disjoint_bc(t1.lub, Type_forward(t1).lub, t2.lub, Type_forward(t2).lub);
        t1.lub.disjoint(t2.lub)) then
          Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Bool(Old.validation.types.BoolType.False()), New.validation.types.Type.Bool(New.validation.types.BoolType.False()));
          Old.validation.types.Ok(Old.validation.types.Type.Bool(Old.validation.types.BoolType.False()))
        else
          if T_O.isUnspecifiedVar(e1_O) && t2.Entity? && (EntityLUB_specified_bc(t2.lub, Type_forward(t2).lub);
          t2.lub.specified()) then
            Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Bool(Old.validation.types.BoolType.False()), New.validation.types.Type.Bool(New.validation.types.BoolType.False()));
            Old.validation.types.Ok(Old.validation.types.Type.Bool(Old.validation.types.BoolType.False()))
          else
            match (e1_O, e2_O) {
              case (PrimitiveLit(EntityUID(u1)), PrimitiveLit(EntityUID(u2))) =>
                if u1 == u2 then
                  Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Bool(Old.validation.types.BoolType.True()), New.validation.types.Type.Bool(New.validation.types.BoolType.True()));
                  Old.validation.types.Ok(Old.validation.types.Type.Bool(Old.validation.types.BoolType.True()))
                else
                  Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Bool(Old.validation.types.BoolType.False()), New.validation.types.Type.Bool(New.validation.types.BoolType.False()));
                  Old.validation.types.Ok(Old.validation.types.Type.Bool(Old.validation.types.BoolType.False()))
              case _ =>
                Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool()), New.validation.types.Type.Bool(New.validation.types.BoolType.AnyBool()));
                Old.validation.types.Ok(Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool()))
            });
      }

      lemma Typechecker_inferIneq_bc(T_O: Old.validation.typechecker.Typechecker, T_N: New.validation.typechecker.Typechecker, op_O: Joint.def.core.BinaryOp, e1_O: Joint.def.core.Expr, e2_O: Joint.def.core.Expr, effs_O: Old.validation.typechecker.Effects, op_N: Joint.def.core.BinaryOp, e1_N: Joint.def.core.Expr, e2_N: Joint.def.core.Expr, effs_N: New.validation.typechecker.Effects)
        decreases Joint.def.core.Expr.BinaryApp(op_O, e1_O, e2_O), 0
        requires op_O == Joint.def.core.BinaryOp.Less() || op_O == Joint.def.core.BinaryOp.LessEq()
        requires T_N == Typechecker_forward(T_O)
        requires op_N == op_O
        requires e1_N == e1_O
        requires e2_N == e2_O
        requires effs_N == Effects_forward(effs_O)
        ensures op_N == Joint.def.core.BinaryOp.Less() || op_N == Joint.def.core.BinaryOp.LessEq()
        ensures T_N.inferIneq(op_N, e1_N, e2_N, effs_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), T_O.inferIneq(op_O, e1_O, e2_O, effs_O))
      {
        assert T_N.inferIneq(op_N, e1_N, e2_N, effs_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), var _ :- (Typechecker_ensureIntType_bc(T_O, T_N, e1_O, effs_O, e1_N, effs_N);
        T_O.ensureIntType(e1_O, effs_O));
        var _ :- (Typechecker_ensureIntType_bc(T_O, T_N, e2_O, effs_O, e2_N, effs_N);
        T_O.ensureIntType(e2_O, effs_O));
        Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool()), New.validation.types.Type.Bool(New.validation.types.BoolType.AnyBool()));
        Old.validation.types.Ok(Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool())));
      }

      lemma {:axiom} Typechecker_tryGetEUID_bc(T_O: Old.validation.typechecker.Typechecker, T_N: New.validation.typechecker.Typechecker, e_O: Joint.def.core.Expr, e_N: Joint.def.core.Expr)
        decreases T_O, e_O
        requires T_N == Typechecker_forward(T_O)
        requires e_N == e_O
        ensures T_N.tryGetEUID(e_N) == Option_forward((x: Joint.def.core.EntityUID) => x, (x: Joint.def.core.EntityUID) => x, T_O.tryGetEUID(e_O))

      lemma Typechecker_tryGetEUIDs_bc(T_O: Old.validation.typechecker.Typechecker, T_N: New.validation.typechecker.Typechecker, e_O: Joint.def.core.Expr, e_N: Joint.def.core.Expr)
        decreases T_O, e_O
        requires T_N == Typechecker_forward(T_O)
        requires e_N == e_O
        ensures T_N.tryGetEUIDs(e_N) == Option_forward((x: set<Joint.def.core.EntityUID>) => x, (x: set<Joint.def.core.EntityUID>) => x, T_O.tryGetEUIDs(e_O))
      {
        match e_O {
          case Set(es) =>
            if (forall e1: Joint.def.core.Expr :: e1 in es ==>
              (Typechecker_tryGetEUID_bc(T_O, T_N, e1, e1);
              T_O.tryGetEUID(e1)).Some?) {
              assert T_N.tryGetEUIDs(e_N) == Option_forward((x: set<Joint.def.core.EntityUID>) => x, (x: set<Joint.def.core.EntityUID>) => x, Joint.def.std.Option.Some(set e1: Joint.def.core.Expr | e1 in es :: (Typechecker_tryGetEUID_bc(T_O, T_N, e1, e1);
              T_O.tryGetEUID(e1)).value));
            } else {
              assert T_N.tryGetEUIDs(e_N) == Option_forward((x: set<Joint.def.core.EntityUID>) => x, (x: set<Joint.def.core.EntityUID>) => x, Joint.def.std.Option.None());
            }
          case _ =>
            assert T_N.tryGetEUIDs(e_N) == Option_forward((x: set<Joint.def.core.EntityUID>) => x, (x: set<Joint.def.core.EntityUID>) => x, Joint.def.std.Option.None());
        }
      }

      lemma Typechecker_getPrincipalOrResource_bc(T_O: Old.validation.typechecker.Typechecker, T_N: New.validation.typechecker.Typechecker, v_O: Joint.def.core.Var, v_N: Joint.def.core.Var)
        decreases T_O, v_O
        requires v_O == Joint.def.core.Var.Principal() || v_O == Joint.def.core.Var.Resource()
        requires T_N == Typechecker_forward(T_O)
        requires v_N == v_O
        ensures v_N == Joint.def.core.Var.Principal() || v_N == Joint.def.core.Var.Resource()
        ensures T_N.getPrincipalOrResource(v_N) == Option_forward((x: Joint.def.core.EntityType) => x, (x: Joint.def.core.EntityType) => x, T_O.getPrincipalOrResource(v_O))
      {
        match v_O {
          case Principal() =>
            assert T_N.getPrincipalOrResource(v_N) == Option_forward((x: Joint.def.core.EntityType) => x, (x: Joint.def.core.EntityType) => x, T_O.reqty.principal);
          case Resource() =>
            assert T_N.getPrincipalOrResource(v_N) == Option_forward((x: Joint.def.core.EntityType) => x, (x: Joint.def.core.EntityType) => x, T_O.reqty.resource);
        }
      }

      lemma Typechecker_inferIn_bc(T_O: Old.validation.typechecker.Typechecker, T_N: New.validation.typechecker.Typechecker, parent_O: Joint.def.core.Expr, e1_O: Joint.def.core.Expr, e2_O: Joint.def.core.Expr, effs_O: Old.validation.typechecker.Effects, parent_N: Joint.def.core.Expr, e1_N: Joint.def.core.Expr, e2_N: Joint.def.core.Expr, effs_N: New.validation.typechecker.Effects)
        decreases parent_O, 0, e2_O
        requires e1_O < parent_O
        requires e2_O < parent_O
        requires T_N == Typechecker_forward(T_O)
        requires parent_N == parent_O
        requires e1_N == e1_O
        requires e2_N == e2_O
        requires effs_N == Effects_forward(effs_O)
        ensures e1_N < parent_N
        ensures e2_N < parent_N
        ensures T_N.inferIn(parent_N, e1_N, e2_N, effs_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), T_O.inferIn(parent_O, e1_O, e2_O, effs_O))
      {
        assert T_N.inferIn(parent_N, e1_N, e2_N, effs_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), var _ :- (Typechecker_ensureEntityType_bc(T_O, T_N, e1_O, effs_O, e1_N, effs_N);
        T_O.ensureEntityType(e1_O, effs_O));
        var _ :- (Typechecker_ensureEntitySetType_bc(T_O, T_N, e2_O, effs_O, e2_N, effs_N);
        T_O.ensureEntitySetType(e2_O, effs_O));
        var (t2, _) := (Typechecker_infer_bc(T_O, T_N, e2_O, effs_O, e2_N, effs_N);
        T_O.infer(e2_O, effs_O)).value;
        if T_O.isUnspecifiedVar(e1_O) && match t2 {
          case Entity(lub) =>
            EntityLUB_specified_bc(lub, EntityLUB_forward(lub));
            lub.specified()
          case Set(Entity(lub)) =>
            EntityLUB_specified_bc(lub, EntityLUB_forward(lub));
            lub.specified()
          case Set(Never()) =>
            false
        } then
          Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Bool(Old.validation.types.BoolType.False()), New.validation.types.Type.Bool(New.validation.types.BoolType.False()));
          Old.validation.types.Ok(Old.validation.types.Type.Bool(Old.validation.types.BoolType.False()))
        else
          match (e1_O, e2_O) {
            case (Var(Action()), _) =>
              Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool()), New.validation.types.Type.Bool(New.validation.types.BoolType.AnyBool()));
              Old.validation.types.Ok(Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool()))
            case (Var(v), PrimitiveLit(EntityUID(u))) =>
              var et := (Typechecker_getPrincipalOrResource_bc(T_O, T_N, v, v);
              T_O.getPrincipalOrResource(v));
              var b := et.None? || (EntityTypeStore_possibleDescendantOf_bc(T_O.ets, T_N.ets, et.value, u.ty, Option_forward((x: Joint.def.core.EntityType) => x, (x: Joint.def.core.EntityType) => x, et).value, u.ty);
              T_O.ets.possibleDescendantOf(et.value, u.ty));
              if b then
                Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool()), New.validation.types.Type.Bool(New.validation.types.BoolType.AnyBool()));
                Old.validation.types.Ok(Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool()))
              else
                Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Bool(Old.validation.types.BoolType.False()), New.validation.types.Type.Bool(New.validation.types.BoolType.False()));
                Old.validation.types.Ok(Old.validation.types.Type.Bool(Old.validation.types.BoolType.False()))
            case (Var(v), Set(_)) =>
              var et := (Typechecker_getPrincipalOrResource_bc(T_O, T_N, v, v);
              T_O.getPrincipalOrResource(v));
              match (Typechecker_tryGetEUIDs_bc(T_O, T_N, e2_O, e2_N);
              T_O.tryGetEUIDs(e2_O)) {
                case Some(euids) =>
                  var es := set euid: Joint.def.core.EntityUID | euid in euids :: euid.ty;
                  var b := et.None? || (EntityTypeStore_possibleDescendantOfSet_bc(T_O.ets, T_N.ets, et.value, es, Option_forward((x: Joint.def.core.EntityType) => x, (x: Joint.def.core.EntityType) => x, et).value, es);
                  T_O.ets.possibleDescendantOfSet(et.value, es));
                  if b then
                    Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool()), New.validation.types.Type.Bool(New.validation.types.BoolType.AnyBool()));
                    Old.validation.types.Ok(Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool()))
                  else
                    Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Bool(Old.validation.types.BoolType.False()), New.validation.types.Type.Bool(New.validation.types.BoolType.False()));
                    Old.validation.types.Ok(Old.validation.types.Type.Bool(Old.validation.types.BoolType.False()))
                case None() =>
                  Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool()), New.validation.types.Type.Bool(New.validation.types.BoolType.AnyBool()));
                  Old.validation.types.Ok(Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool()))
              }
            case (PrimitiveLit(EntityUID(u1)), PrimitiveLit(EntityUID(u2))) =>
              if isAction_bc(u1.ty, u1.ty);
              Old.validation.types.isAction(u1.ty) then
                if ActionStore_descendantOf_bc(T_O.acts, T_N.acts, u1, u2, u1, u2);
                T_O.acts.descendantOf(u1, u2) then
                  Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool()), New.validation.types.Type.Bool(New.validation.types.BoolType.AnyBool()));
                  Old.validation.types.Ok(Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool()))
                else
                  Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Bool(Old.validation.types.BoolType.False()), New.validation.types.Type.Bool(New.validation.types.BoolType.False()));
                  Old.validation.types.Ok(Old.validation.types.Type.Bool(Old.validation.types.BoolType.False()))
              else
                var b := (EntityTypeStore_possibleDescendantOf_bc(T_O.ets, T_N.ets, u1.ty, u2.ty, u1.ty, u2.ty);
                T_O.ets.possibleDescendantOf(u1.ty, u2.ty));
                if b then
                  Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool()), New.validation.types.Type.Bool(New.validation.types.BoolType.AnyBool()));
                  Old.validation.types.Ok(Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool()))
                else
                  Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Bool(Old.validation.types.BoolType.False()), New.validation.types.Type.Bool(New.validation.types.BoolType.False()));
                  Old.validation.types.Ok(Old.validation.types.Type.Bool(Old.validation.types.BoolType.False()))
            case (PrimitiveLit(EntityUID(u)), Set(_)) =>
              match (Typechecker_tryGetEUIDs_bc(T_O, T_N, e2_O, e2_N);
              T_O.tryGetEUIDs(e2_O)) {
                case Some(euids) =>
                  if isAction_bc(u.ty, u.ty);
                  Old.validation.types.isAction(u.ty) then
                    if ActionStore_descendantOfSet_bc(T_O.acts, T_N.acts, u, euids, u, euids);
                    T_O.acts.descendantOfSet(u, euids) then
                      Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool()), New.validation.types.Type.Bool(New.validation.types.BoolType.AnyBool()));
                      Old.validation.types.Ok(Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool()))
                    else
                      Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Bool(Old.validation.types.BoolType.False()), New.validation.types.Type.Bool(New.validation.types.BoolType.False()));
                      Old.validation.types.Ok(Old.validation.types.Type.Bool(Old.validation.types.BoolType.False()))
                  else
                    var es := set euid: Joint.def.core.EntityUID | euid in euids :: euid.ty;
                    var b := (EntityTypeStore_possibleDescendantOfSet_bc(T_O.ets, T_N.ets, u.ty, es, u.ty, es);
                    T_O.ets.possibleDescendantOfSet(u.ty, es));
                    if b then
                      Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool()), New.validation.types.Type.Bool(New.validation.types.BoolType.AnyBool()));
                      Old.validation.types.Ok(Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool()))
                    else
                      Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Bool(Old.validation.types.BoolType.False()), New.validation.types.Type.Bool(New.validation.types.BoolType.False()));
                      Old.validation.types.Ok(Old.validation.types.Type.Bool(Old.validation.types.BoolType.False()))
                case None() =>
                  Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool()), New.validation.types.Type.Bool(New.validation.types.BoolType.AnyBool()));
                  Old.validation.types.Ok(Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool()))
              }
            case _ =>
              Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool()), New.validation.types.Type.Bool(New.validation.types.BoolType.AnyBool()));
              Old.validation.types.Ok(Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool()))
          });
      }

      lemma Typechecker_inferContainsAnyAll_bc(T_O: Old.validation.typechecker.Typechecker, T_N: New.validation.typechecker.Typechecker, b_O: Joint.def.core.BinaryOp, e1_O: Joint.def.core.Expr, e2_O: Joint.def.core.Expr, effs_O: Old.validation.typechecker.Effects, b_N: Joint.def.core.BinaryOp, e1_N: Joint.def.core.Expr, e2_N: Joint.def.core.Expr, effs_N: New.validation.typechecker.Effects)
        decreases Joint.def.core.Expr.BinaryApp(b_O, e1_O, e2_O), 0
        requires b_O == Joint.def.core.BinaryOp.ContainsAny() || b_O == Joint.def.core.BinaryOp.ContainsAll()
        requires T_N == Typechecker_forward(T_O)
        requires b_N == b_O
        requires e1_N == e1_O
        requires e2_N == e2_O
        requires effs_N == Effects_forward(effs_O)
        ensures b_N == Joint.def.core.BinaryOp.ContainsAny() || b_N == Joint.def.core.BinaryOp.ContainsAll()
        ensures T_N.inferContainsAnyAll(b_N, e1_N, e2_N, effs_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), T_O.inferContainsAnyAll(b_O, e1_O, e2_O, effs_O))
      {
        assert T_N.inferContainsAnyAll(b_N, e1_N, e2_N, effs_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), var s1 :- (Typechecker_inferSetType_bc(T_O, T_N, e1_O, effs_O, e1_N, effs_N);
        T_O.inferSetType(e1_O, effs_O));
        var s2 :- (Typechecker_inferSetType_bc(T_O, T_N, e2_O, effs_O, e2_N, effs_N);
        T_O.inferSetType(e2_O, effs_O));
        Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool()), New.validation.types.Type.Bool(New.validation.types.BoolType.AnyBool()));
        Old.validation.types.Ok(Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool())));
      }

      lemma Typechecker_inferContains_bc(T_O: Old.validation.typechecker.Typechecker, T_N: New.validation.typechecker.Typechecker, e1_O: Joint.def.core.Expr, e2_O: Joint.def.core.Expr, effs_O: Old.validation.typechecker.Effects, e1_N: Joint.def.core.Expr, e2_N: Joint.def.core.Expr, effs_N: New.validation.typechecker.Effects)
        decreases Joint.def.core.Expr.BinaryApp(Joint.def.core.BinaryOp.Contains(), e1_O, e2_O), 0
        requires T_N == Typechecker_forward(T_O)
        requires e1_N == e1_O
        requires e2_N == e2_O
        requires effs_N == Effects_forward(effs_O)
        ensures T_N.inferContains(e1_N, e2_N, effs_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), T_O.inferContains(e1_O, e2_O, effs_O))
      {
        assert T_N.inferContains(e1_N, e2_N, effs_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), var s :- (Typechecker_inferSetType_bc(T_O, T_N, e1_O, effs_O, e1_N, effs_N);
        T_O.inferSetType(e1_O, effs_O));
        var t :- (Typechecker_infer_bc(T_O, T_N, e2_O, effs_O, e2_N, effs_N);
        T_O.infer(e2_O, effs_O));
        Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool()), New.validation.types.Type.Bool(New.validation.types.BoolType.AnyBool()));
        Old.validation.types.Ok(Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool())));
      }

      lemma Typechecker_inferRecord_bc(T_O: Old.validation.typechecker.Typechecker, T_N: New.validation.typechecker.Typechecker, e_O: Joint.def.core.Expr, r_O: seq<(Joint.def.core.Attr,Joint.def.core.Expr)>, effs_O: Old.validation.typechecker.Effects, e_N: Joint.def.core.Expr, r_N: seq<(Joint.def.core.Attr,Joint.def.core.Expr)>, effs_N: New.validation.typechecker.Effects)
        decreases e_O, 0, r_O
        requires forall i: int :: 0 <= i && i < |r_O| ==> r_O[i] < e_O
        requires T_N == Typechecker_forward(T_O)
        requires e_N == e_O
        requires r_N == r_O
        requires effs_N == Effects_forward(effs_O)
        ensures forall i: int :: 0 <= i && i < |r_N| ==> r_N[i] < e_N
        ensures T_N.inferRecord(e_N, r_N, effs_N) == Result_forward((x: Old.validation.types.RecordType) => RecordType_forward(x), (x: New.validation.types.RecordType) => RecordType_backward(x), T_O.inferRecord(e_O, r_O, effs_O))
      {
        reveal T_O.inferRecord();
        reveal T_N.inferRecord();
        if (r_O == []) {
          Ok_bc((x: Old.validation.types.RecordType) => RecordType_forward(x), (x: New.validation.types.RecordType) => RecordType_backward(x), Old.validation.types.RecordType.RecordType(map [], Old.validation.types.AttrsTag.ClosedAttributes()), New.validation.types.RecordType.RecordType(map [], New.validation.types.AttrsTag.ClosedAttributes()));
          assert T_N.inferRecord(e_N, r_N, effs_N) == Result_forward((x: Old.validation.types.RecordType) => RecordType_forward(x), (x: New.validation.types.RecordType) => RecordType_backward(x), Old.validation.types.Ok(Old.validation.types.RecordType.RecordType(map [], Old.validation.types.AttrsTag.ClosedAttributes())));
        } else {
          var k := r_O[0].0;
          assert T_N.inferRecord(e_N, r_N, effs_N) == Result_forward((x: Old.validation.types.RecordType) => RecordType_forward(x), (x: New.validation.types.RecordType) => RecordType_backward(x), var (t, _) :- (Typechecker_infer_bc(T_O, T_N, r_O[0].1, effs_O, r_N[0].1, effs_N);
          T_O.infer(r_O[0].1, effs_O));
          assert r_O[0] < e_O;
          var m :- (Typechecker_inferRecord_bc(T_O, T_N, e_O, r_O[1..], effs_O, e_N, r_N[1..], effs_N);
          T_O.inferRecord(e_O, r_O[1..], effs_O));
          Ok_bc((x: Old.validation.types.RecordType) => RecordType_forward(x), (x: New.validation.types.RecordType) => RecordType_backward(x), Old.validation.types.RecordType.RecordType(if k in m.attrs.Keys then m.attrs else m.attrs[k := Old.validation.types.AttrType.AttrType(t, true)], Old.validation.types.AttrsTag.ClosedAttributes()), New.validation.types.RecordType.RecordType(if k in RecordType_forward(m).attrs.Keys then RecordType_forward(m).attrs else RecordType_forward(m).attrs[k := New.validation.types.AttrType.AttrType(Type_forward(t), true)], New.validation.types.AttrsTag.ClosedAttributes()));
          Old.validation.types.Ok(Old.validation.types.RecordType.RecordType(if k in m.attrs.Keys then m.attrs else m.attrs[k := Old.validation.types.AttrType.AttrType(t, true)], Old.validation.types.AttrsTag.ClosedAttributes())));
        }
      }

      lemma Typechecker_inferHasAttrHelper_bc(T_O: Old.validation.typechecker.Typechecker, T_N: New.validation.typechecker.Typechecker, e_O: Joint.def.core.Expr, k_O: Joint.def.core.Attr, rt_O: Old.validation.types.RecordType, effs_O: Old.validation.typechecker.Effects, knownToExist_O: bool, e_N: Joint.def.core.Expr, k_N: Joint.def.core.Attr, rt_N: New.validation.types.RecordType, effs_N: New.validation.typechecker.Effects, knownToExist_N: bool)
        decreases T_O, e_O, k_O, rt_O, effs_O, knownToExist_O
        requires T_N == Typechecker_forward(T_O)
        requires e_N == e_O
        requires k_N == k_O
        requires rt_N == RecordType_forward(rt_O)
        requires effs_N == Effects_forward(effs_O)
        requires knownToExist_N == knownToExist_O
        ensures T_N.inferHasAttrHelper(e_N, k_N, rt_N, effs_N, knownToExist_N) == Result_forward((x: (Old.validation.types.Type,Old.validation.typechecker.Effects)) => (Type_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.Type,New.validation.typechecker.Effects)) => (Type_backward(x.0), Effects_backward(x.1)), T_O.inferHasAttrHelper(e_O, k_O, rt_O, effs_O, knownToExist_O))
      {
        if (k_O in rt_O.attrs) {
          if (rt_O.attrs[k_O].isRequired && knownToExist_O) {
            Typechecker_wrap_bc(T_O, T_N, Old.validation.types.Ok(Old.validation.types.Type.Bool(Old.validation.types.BoolType.True())), New.validation.types.Ok(New.validation.types.Type.Bool(New.validation.types.BoolType.True())));
            assert T_N.inferHasAttrHelper(e_N, k_N, rt_N, effs_N, knownToExist_N) == Result_forward((x: (Old.validation.types.Type,Old.validation.typechecker.Effects)) => (Type_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.Type,New.validation.typechecker.Effects)) => (Type_backward(x.0), Effects_backward(x.1)), T_O.wrap(Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Bool(Old.validation.types.BoolType.True()), New.validation.types.Type.Bool(New.validation.types.BoolType.True()));
            Old.validation.types.Ok(Old.validation.types.Type.Bool(Old.validation.types.BoolType.True()))));
          } else {
            if (Effects_contains_bc(effs_O, effs_N, e_O, k_O, e_N, k_N);
            effs_O.contains(e_O, k_O)) {
              Typechecker_wrap_bc(T_O, T_N, Old.validation.types.Ok(Old.validation.types.Type.Bool(Old.validation.types.BoolType.True())), New.validation.types.Ok(New.validation.types.Type.Bool(New.validation.types.BoolType.True())));
              assert T_N.inferHasAttrHelper(e_N, k_N, rt_N, effs_N, knownToExist_N) == Result_forward((x: (Old.validation.types.Type,Old.validation.typechecker.Effects)) => (Type_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.Type,New.validation.typechecker.Effects)) => (Type_backward(x.0), Effects_backward(x.1)), T_O.wrap(Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Bool(Old.validation.types.BoolType.True()), New.validation.types.Type.Bool(New.validation.types.BoolType.True()));
              Old.validation.types.Ok(Old.validation.types.Type.Bool(Old.validation.types.BoolType.True()))));
            } else {
              Ok_bc((x: (Old.validation.types.Type,Old.validation.typechecker.Effects)) => (Type_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.Type,New.validation.typechecker.Effects)) => (Type_backward(x.0), Effects_backward(x.1)), (Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool()), Old.validation.typechecker.Effects.singleton(e_O, k_O)), (New.validation.types.Type.Bool(New.validation.types.BoolType.AnyBool()), New.validation.typechecker.Effects.singleton(e_N, k_N)));
              assert T_N.inferHasAttrHelper(e_N, k_N, rt_N, effs_N, knownToExist_N) == Result_forward((x: (Old.validation.types.Type,Old.validation.typechecker.Effects)) => (Type_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.Type,New.validation.typechecker.Effects)) => (Type_backward(x.0), Effects_backward(x.1)), Old.validation.types.Ok((Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool()), Effects_singleton_bc(e_O, k_O, e_N, k_N);
              Old.validation.typechecker.Effects.singleton(e_O, k_O))));
            }
          }
        } else {
          if (RecordType_isOpen_bc(rt_O, rt_N);
          rt_O.isOpen()) {
            Typechecker_wrap_bc(T_O, T_N, Old.validation.types.Ok(Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool())), New.validation.types.Ok(New.validation.types.Type.Bool(New.validation.types.BoolType.AnyBool())));
            assert T_N.inferHasAttrHelper(e_N, k_N, rt_N, effs_N, knownToExist_N) == Result_forward((x: (Old.validation.types.Type,Old.validation.typechecker.Effects)) => (Type_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.Type,New.validation.typechecker.Effects)) => (Type_backward(x.0), Effects_backward(x.1)), T_O.wrap(Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool()), New.validation.types.Type.Bool(New.validation.types.BoolType.AnyBool()));
            Old.validation.types.Ok(Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool()))));
          } else {
            Typechecker_wrap_bc(T_O, T_N, Old.validation.types.Ok(Old.validation.types.Type.Bool(Old.validation.types.BoolType.False())), New.validation.types.Ok(New.validation.types.Type.Bool(New.validation.types.BoolType.False())));
            assert T_N.inferHasAttrHelper(e_N, k_N, rt_N, effs_N, knownToExist_N) == Result_forward((x: (Old.validation.types.Type,Old.validation.typechecker.Effects)) => (Type_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.Type,New.validation.typechecker.Effects)) => (Type_backward(x.0), Effects_backward(x.1)), T_O.wrap(Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Bool(Old.validation.types.BoolType.False()), New.validation.types.Type.Bool(New.validation.types.BoolType.False()));
            Old.validation.types.Ok(Old.validation.types.Type.Bool(Old.validation.types.BoolType.False()))));
          }
        }
      }

      lemma Typechecker_inferHasAttr_bc(T_O: Old.validation.typechecker.Typechecker, T_N: New.validation.typechecker.Typechecker, e_O: Joint.def.core.Expr, k_O: Joint.def.core.Attr, effs_O: Old.validation.typechecker.Effects, e_N: Joint.def.core.Expr, k_N: Joint.def.core.Attr, effs_N: New.validation.typechecker.Effects)
        decreases Joint.def.core.Expr.HasAttr(e_O, k_O), 0
        requires T_N == Typechecker_forward(T_O)
        requires e_N == e_O
        requires k_N == k_O
        requires effs_N == Effects_forward(effs_O)
        ensures T_N.inferHasAttr(e_N, k_N, effs_N) == Result_forward((x: (Old.validation.types.Type,Old.validation.typechecker.Effects)) => (Type_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.Type,New.validation.typechecker.Effects)) => (Type_backward(x.0), Effects_backward(x.1)), T_O.inferHasAttr(e_O, k_O, effs_O))
      {
        assert T_N.inferHasAttr(e_N, k_N, effs_N) == Result_forward((x: (Old.validation.types.Type,Old.validation.typechecker.Effects)) => (Type_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.Type,New.validation.typechecker.Effects)) => (Type_backward(x.0), Effects_backward(x.1)), var ret :- (Typechecker_inferRecordEntityType_bc(T_O, T_N, e_O, effs_O, e_N, effs_N);
        T_O.inferRecordEntityType(e_O, effs_O));
        match ret {
          case Record(rt) =>
            Typechecker_inferHasAttrHelper_bc(T_O, T_N, e_O, k_O, rt, effs_O, true, e_N, k_N, RecordType_forward(rt), effs_N, true);
            T_O.inferHasAttrHelper(e_O, k_O, rt, effs_O, true)
          case Entity(lub) =>
            if !(EntityTypeStore_isAttrPossible_bc(T_O.ets, T_N.ets, lub, k_O, EntityLUB_forward(lub), k_N);
            T_O.ets.isAttrPossible(lub, k_O)) then
              Typechecker_wrap_bc(T_O, T_N, Old.validation.types.Ok(Old.validation.types.Type.Bool(Old.validation.types.BoolType.False())), New.validation.types.Ok(New.validation.types.Type.Bool(New.validation.types.BoolType.False())));
              T_O.wrap(Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Bool(Old.validation.types.BoolType.False()), New.validation.types.Type.Bool(New.validation.types.BoolType.False()));
              Old.validation.types.Ok(Old.validation.types.Type.Bool(Old.validation.types.BoolType.False())))
            else
              var rt :- T_O.ets.getLubRecordType(lub);
              Typechecker_inferHasAttrHelper_bc(T_O, T_N, e_O, k_O, rt, effs_O, false, e_N, k_N, RecordType_forward(rt), effs_N, false);
              T_O.inferHasAttrHelper(e_O, k_O, rt, effs_O, false)
        });
      }

      lemma Typechecker_inferLike_bc(T_O: Old.validation.typechecker.Typechecker, T_N: New.validation.typechecker.Typechecker, p_O: Joint.def.core.Pattern, e_O: Joint.def.core.Expr, effs_O: Old.validation.typechecker.Effects, p_N: Joint.def.core.Pattern, e_N: Joint.def.core.Expr, effs_N: New.validation.typechecker.Effects)
        decreases Joint.def.core.Expr.UnaryApp(Joint.def.core.UnaryOp.Like(p_O), e_O), 0
        requires T_N == Typechecker_forward(T_O)
        requires p_N == p_O
        requires e_N == e_O
        requires effs_N == Effects_forward(effs_O)
        ensures T_N.inferLike(p_N, e_N, effs_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), T_O.inferLike(p_O, e_O, effs_O))
      {
        assert T_N.inferLike(p_N, e_N, effs_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), var _ :- (Typechecker_ensureStringType_bc(T_O, T_N, e_O, effs_O, e_N, effs_N);
        T_O.ensureStringType(e_O, effs_O));
        Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool()), New.validation.types.Type.Bool(New.validation.types.BoolType.AnyBool()));
        Old.validation.types.Ok(Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool())));
      }

      lemma Typechecker_inferArith1_bc(T_O: Old.validation.typechecker.Typechecker, T_N: New.validation.typechecker.Typechecker, op_O: Joint.def.core.UnaryOp, e_O: Joint.def.core.Expr, effs_O: Old.validation.typechecker.Effects, op_N: Joint.def.core.UnaryOp, e_N: Joint.def.core.Expr, effs_N: New.validation.typechecker.Effects)
        decreases Joint.def.core.Expr.UnaryApp(op_O, e_O), 0
        requires op_O.Neg? || op_O.MulBy?
        requires T_N == Typechecker_forward(T_O)
        requires op_N == op_O
        requires e_N == e_O
        requires effs_N == Effects_forward(effs_O)
        ensures op_N.Neg? || op_N.MulBy?
        ensures T_N.inferArith1(op_N, e_N, effs_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), T_O.inferArith1(op_O, e_O, effs_O))
      {
        assert T_N.inferArith1(op_N, e_N, effs_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), var _ :- (Typechecker_ensureIntType_bc(T_O, T_N, e_O, effs_O, e_N, effs_N);
        T_O.ensureIntType(e_O, effs_O));
        Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Int(), New.validation.types.Type.Int());
        Old.validation.types.Ok(Old.validation.types.Type.Int()));
      }

      lemma Typechecker_inferArith2_bc(T_O: Old.validation.typechecker.Typechecker, T_N: New.validation.typechecker.Typechecker, op_O: Joint.def.core.BinaryOp, e1_O: Joint.def.core.Expr, e2_O: Joint.def.core.Expr, effs_O: Old.validation.typechecker.Effects, op_N: Joint.def.core.BinaryOp, e1_N: Joint.def.core.Expr, e2_N: Joint.def.core.Expr, effs_N: New.validation.typechecker.Effects)
        decreases Joint.def.core.Expr.BinaryApp(op_O, e1_O, e2_O), 0
        requires op_O == Joint.def.core.BinaryOp.Add() || op_O == Joint.def.core.BinaryOp.Sub()
        requires T_N == Typechecker_forward(T_O)
        requires op_N == op_O
        requires e1_N == e1_O
        requires e2_N == e2_O
        requires effs_N == Effects_forward(effs_O)
        ensures op_N == Joint.def.core.BinaryOp.Add() || op_N == Joint.def.core.BinaryOp.Sub()
        ensures T_N.inferArith2(op_N, e1_N, e2_N, effs_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), T_O.inferArith2(op_O, e1_O, e2_O, effs_O))
      {
        assert T_N.inferArith2(op_N, e1_N, e2_N, effs_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), var _ :- (Typechecker_ensureIntType_bc(T_O, T_N, e1_O, effs_O, e1_N, effs_N);
        T_O.ensureIntType(e1_O, effs_O));
        var _ :- (Typechecker_ensureIntType_bc(T_O, T_N, e2_O, effs_O, e2_N, effs_N);
        T_O.ensureIntType(e2_O, effs_O));
        Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Int(), New.validation.types.Type.Int());
        Old.validation.types.Ok(Old.validation.types.Type.Int()));
      }

      lemma Typechecker_inferGetAttr_bc(T_O: Old.validation.typechecker.Typechecker, T_N: New.validation.typechecker.Typechecker, e_O: Joint.def.core.Expr, k_O: Joint.def.core.Attr, effs_O: Old.validation.typechecker.Effects, e_N: Joint.def.core.Expr, k_N: Joint.def.core.Attr, effs_N: New.validation.typechecker.Effects)
        decreases Joint.def.core.Expr.GetAttr(e_O, k_O), 0
        requires T_N == Typechecker_forward(T_O)
        requires e_N == e_O
        requires k_N == k_O
        requires effs_N == Effects_forward(effs_O)
        ensures T_N.inferGetAttr(e_N, k_N, effs_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), T_O.inferGetAttr(e_O, k_O, effs_O))
      {
        assert T_N.inferGetAttr(e_N, k_N, effs_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), var ret :- (Typechecker_inferRecordEntityType_bc(T_O, T_N, e_O, effs_O, e_N, effs_N);
        T_O.inferRecordEntityType(e_O, effs_O));
        match ret {
          case Record(rt) =>
            if k_O in rt.attrs && (rt.attrs[k_O].isRequired || (Effects_contains_bc(effs_O, effs_N, e_O, k_O, e_N, k_N);
            effs_O.contains(e_O, k_O))) then
              Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), rt.attrs[k_O].ty, RecordType_forward(rt).attrs[k_N].ty);
              Old.validation.types.Ok(rt.attrs[k_O].ty)
            else
              Err_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.TypeError.AttrNotFound(Old.validation.types.Type.Record(rt), k_O), New.validation.types.TypeError.AttrNotFound(New.validation.types.Type.Record(RecordType_forward(rt)), k_N));
              Old.validation.types.Err(Old.validation.types.TypeError.AttrNotFound(Old.validation.types.Type.Record(rt), k_O))
          case Entity(lub) =>
            var rt :- T_O.ets.getLubRecordType(lub);
            if k_O in rt.attrs && (rt.attrs[k_O].isRequired || (Effects_contains_bc(effs_O, effs_N, e_O, k_O, e_N, k_N);
            effs_O.contains(e_O, k_O))) then
              Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), rt.attrs[k_O].ty, RecordType_forward(rt).attrs[k_N].ty);
              Old.validation.types.Ok(rt.attrs[k_O].ty)
            else
              Err_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.TypeError.AttrNotFound(Old.validation.types.Type.Entity(lub), k_O), New.validation.types.TypeError.AttrNotFound(New.validation.types.Type.Entity(EntityLUB_forward(lub)), k_N));
              Old.validation.types.Err(Old.validation.types.TypeError.AttrNotFound(Old.validation.types.Type.Entity(lub), k_O))
        });
      }

      lemma Typechecker_inferSet_bc(T_O: Old.validation.typechecker.Typechecker, T_N: New.validation.typechecker.Typechecker, e_O: Joint.def.core.Expr, r_O: seq<Joint.def.core.Expr>, effs_O: Old.validation.typechecker.Effects, e_N: Joint.def.core.Expr, r_N: seq<Joint.def.core.Expr>, effs_N: New.validation.typechecker.Effects)
        decreases e_O, 0, r_O
        requires forall i: int :: 0 <= i && i < |r_O| ==> r_O[i] < e_O
        requires T_N == Typechecker_forward(T_O)
        requires e_N == e_O
        requires r_N == r_O
        requires effs_N == Effects_forward(effs_O)
        ensures forall i: int :: 0 <= i && i < |r_N| ==> r_N[i] < e_N
        ensures T_N.inferSet(e_N, r_N, effs_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), T_O.inferSet(e_O, r_O, effs_O))
      {
        if (r_O == []) {
          Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Never(), New.validation.types.Type.Never());
          assert T_N.inferSet(e_N, r_N, effs_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Ok(Old.validation.types.Type.Never()));
        } else {
          assert T_N.inferSet(e_N, r_N, effs_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), var (t, _) :- (Typechecker_infer_bc(T_O, T_N, r_O[0], effs_O, r_N[0], effs_N);
          T_O.infer(r_O[0], effs_O));
          var t1 :- (Typechecker_inferSet_bc(T_O, T_N, e_O, r_O[1..], effs_O, e_N, r_N[1..], effs_N);
          T_O.inferSet(e_O, r_O[1..], effs_O));
          var t2 :- Old.validation.subtyping.lubOpt(t, t1);
          Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), t2, Type_forward(t2));
          Old.validation.types.Ok(t2));
        }
      }

      lemma Typechecker_wrap_bc(T_O: Old.validation.typechecker.Typechecker, T_N: New.validation.typechecker.Typechecker, t_O: Old.validation.types.Result<Old.validation.types.Type>, t_N: New.validation.types.Result<New.validation.types.Type>)
        decreases T_O, t_O
        requires T_N == Typechecker_forward(T_O)
        requires t_N == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), t_O)
        ensures T_N.wrap(t_N) == Result_forward((x: (Old.validation.types.Type,Old.validation.typechecker.Effects)) => (Type_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.Type,New.validation.typechecker.Effects)) => (Type_backward(x.0), Effects_backward(x.1)), T_O.wrap(t_O))
      {
        assert T_N.wrap(t_N) == Result_forward((x: (Old.validation.types.Type,Old.validation.typechecker.Effects)) => (Type_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.Type,New.validation.typechecker.Effects)) => (Type_backward(x.0), Effects_backward(x.1)), t_O.Map((t0: Old.validation.types.Type) => (t0, Effects_empty_bc();
        Old.validation.typechecker.Effects.empty())));
      }

      lemma Typechecker_inferCallArgs_bc(T_O: Old.validation.typechecker.Typechecker, T_N: New.validation.typechecker.Typechecker, e_O: Joint.def.core.Expr, args_O: seq<Joint.def.core.Expr>, tys_O: seq<Old.validation.types.Type>, effs_O: Old.validation.typechecker.Effects, e_N: Joint.def.core.Expr, args_N: seq<Joint.def.core.Expr>, tys_N: seq<New.validation.types.Type>, effs_N: New.validation.typechecker.Effects)
        decreases e_O, 0, args_O
        requires |args_O| == |tys_O|
        requires forall i: int :: 0 <= i && i < |args_O| ==> args_O[i] < e_O
        requires T_N == Typechecker_forward(T_O)
        requires e_N == e_O
        requires args_N == args_O
        requires tys_N == Translations.MapBuiltinTypes.Seq((sq: Old.validation.types.Type) => Type_forward(sq), tys_O)
        requires effs_N == Effects_forward(effs_O)
        ensures |args_N| == |tys_N|
        ensures forall i: int :: 0 <= i && i < |args_N| ==> args_N[i] < e_N
        ensures T_N.inferCallArgs(e_N, args_N, tys_N, effs_N) == Result_forward((x: ()) => (), (x: ()) => (), T_O.inferCallArgs(e_O, args_O, tys_O, effs_O))
      {
        if (args_O == []) {
          Ok_bc((x: ()) => (), (x: ()) => (), (), ());
          assert T_N.inferCallArgs(e_N, args_N, tys_N, effs_N) == Result_forward((x: ()) => (), (x: ()) => (), Old.validation.types.Ok(()));
        } else {
          assert T_N.inferCallArgs(e_N, args_N, tys_N, effs_N) == Result_forward((x: ()) => (), (x: ()) => (), var (t, _) :- (Typechecker_infer_bc(T_O, T_N, args_O[0], effs_O, args_N[0], effs_N);
          T_O.infer(args_O[0], effs_O));
          var _ :- (Typechecker_ensureSubty_bc(T_O, T_N, t, tys_O[0], Type_forward(t), tys_N[0]);
          T_O.ensureSubty(t, tys_O[0]));
          Typechecker_inferCallArgs_bc(T_O, T_N, e_O, args_O[1..], tys_O[1..], effs_O, e_N, args_N[1..], tys_N[1..], effs_N);
          T_O.inferCallArgs(e_O, args_O[1..], tys_O[1..], effs_O));
        }
      }

      lemma Typechecker_inferCall_bc(T_O: Old.validation.typechecker.Typechecker, T_N: New.validation.typechecker.Typechecker, e_O: Joint.def.core.Expr, name_O: Joint.def.base.Name, args_O: seq<Joint.def.core.Expr>, effs_O: Old.validation.typechecker.Effects, e_N: Joint.def.core.Expr, name_N: Joint.def.base.Name, args_N: seq<Joint.def.core.Expr>, effs_N: New.validation.typechecker.Effects)
        decreases e_O, 0
        requires forall i: int :: 0 <= i && i < |args_O| ==> args_O[i] < e_O
        requires T_N == Typechecker_forward(T_O)
        requires e_N == e_O
        requires name_N == name_O
        requires args_N == args_O
        requires effs_N == Effects_forward(effs_O)
        ensures forall i: int :: 0 <= i && i < |args_N| ==> args_N[i] < e_N
        ensures T_N.inferCall(e_N, name_N, args_N, effs_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), T_O.inferCall(e_O, name_O, args_O, effs_O))
      {
        if (name_O in Old.validation.ext.extFunTypes.Keys) {
          var ty := Old.validation.ext.extFunTypes[name_O];
          assert T_N.inferCall(e_N, name_N, args_N, effs_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), var _ :- (if |args_O| == |ty.args| then
            Ok_bc((x: ()) => (), (x: ()) => (), (), ());
            Old.validation.types.Ok(())
          else
            Err_bc((x: ()) => (), (x: ()) => (), Old.validation.types.TypeError.ExtensionErr(Joint.def.core.Expr.Call(name_O, args_O)), New.validation.types.TypeError.ExtensionErr(Joint.def.core.Expr.Call(name_N, args_N)));
            Old.validation.types.Err(Old.validation.types.TypeError.ExtensionErr(Joint.def.core.Expr.Call(name_O, args_O))));
          var _ :- (Typechecker_inferCallArgs_bc(T_O, T_N, e_O, args_O, ty.args, effs_O, e_N, args_N, ExtFunType_forward(ty).args, effs_N);
          T_O.inferCallArgs(e_O, args_O, ty.args, effs_O));
          var _ :- match ty.check {
            case Some(f) =>
              f(args_O)
            case None() =>
              Ok_bc((x: ()) => (), (x: ()) => (), (), ());
              Old.validation.types.Ok(())
          };
          Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), ty.ret, ExtFunType_forward(ty).ret);
          Old.validation.types.Ok(ty.ret));
        } else {
          Err_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.TypeError.ExtensionErr(Joint.def.core.Expr.Call(name_O, args_O)), New.validation.types.TypeError.ExtensionErr(Joint.def.core.Expr.Call(name_N, args_N)));
          assert T_N.inferCall(e_N, name_N, args_N, effs_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Err(Old.validation.types.TypeError.ExtensionErr(Joint.def.core.Expr.Call(name_O, args_O))));
        }
      }

      lemma Typechecker_infer_bc(T_O: Old.validation.typechecker.Typechecker, T_N: New.validation.typechecker.Typechecker, e_O: Joint.def.core.Expr, effs_O: Old.validation.typechecker.Effects, e_N: Joint.def.core.Expr, effs_N: New.validation.typechecker.Effects)
        decreases e_O, 1
        requires T_N == Typechecker_forward(T_O)
        requires e_N == e_O
        requires effs_N == Effects_forward(effs_O)
        ensures T_N.infer(e_N, effs_N) == Result_forward((x: (Old.validation.types.Type,Old.validation.typechecker.Effects)) => (Type_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.Type,New.validation.typechecker.Effects)) => (Type_backward(x.0), Effects_backward(x.1)), T_O.infer(e_O, effs_O))
      {
        match e_O {
          case PrimitiveLit(p) =>
            Typechecker_wrap_bc(T_O, T_N, T_O.inferPrim(p), T_N.inferPrim(p));
            assert T_N.infer(e_N, effs_N) == Result_forward((x: (Old.validation.types.Type,Old.validation.typechecker.Effects)) => (Type_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.Type,New.validation.typechecker.Effects)) => (Type_backward(x.0), Effects_backward(x.1)), T_O.wrap(Typechecker_inferPrim_bc(T_O, T_N, p, p);
            T_O.inferPrim(p)));
          case Var(x) =>
            Typechecker_wrap_bc(T_O, T_N, T_O.inferVar(x), T_N.inferVar(x));
            assert T_N.infer(e_N, effs_N) == Result_forward((x: (Old.validation.types.Type,Old.validation.typechecker.Effects)) => (Type_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.Type,New.validation.typechecker.Effects)) => (Type_backward(x.0), Effects_backward(x.1)), T_O.wrap(Typechecker_inferVar_bc(T_O, T_N, x, x);
            T_O.inferVar(x)));
          case If(e1, e2, e3) =>
            Typechecker_inferIf_bc(T_O, T_N, e1, e2, e3, effs_O, e1, e2, e3, effs_N);
            assert T_N.infer(e_N, effs_N) == Result_forward((x: (Old.validation.types.Type,Old.validation.typechecker.Effects)) => (Type_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.Type,New.validation.typechecker.Effects)) => (Type_backward(x.0), Effects_backward(x.1)), T_O.inferIf(e1, e2, e3, effs_O));
          case And(e1, e2) =>
            Typechecker_inferAnd_bc(T_O, T_N, e1, e2, effs_O, e1, e2, effs_N);
            assert T_N.infer(e_N, effs_N) == Result_forward((x: (Old.validation.types.Type,Old.validation.typechecker.Effects)) => (Type_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.Type,New.validation.typechecker.Effects)) => (Type_backward(x.0), Effects_backward(x.1)), T_O.inferAnd(e1, e2, effs_O));
          case Or(e1, e2) =>
            Typechecker_inferOr_bc(T_O, T_N, e1, e2, effs_O, e1, e2, effs_N);
            assert T_N.infer(e_N, effs_N) == Result_forward((x: (Old.validation.types.Type,Old.validation.typechecker.Effects)) => (Type_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.Type,New.validation.typechecker.Effects)) => (Type_backward(x.0), Effects_backward(x.1)), T_O.inferOr(e1, e2, effs_O));
          case UnaryApp(Not(), e1) =>
            Typechecker_wrap_bc(T_O, T_N, T_O.inferNot(e1, effs_O), T_N.inferNot(e1, effs_N));
            assert T_N.infer(e_N, effs_N) == Result_forward((x: (Old.validation.types.Type,Old.validation.typechecker.Effects)) => (Type_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.Type,New.validation.typechecker.Effects)) => (Type_backward(x.0), Effects_backward(x.1)), T_O.wrap(Typechecker_inferNot_bc(T_O, T_N, e1, effs_O, e1, effs_N);
            T_O.inferNot(e1, effs_O)));
          case UnaryApp(Neg(), e1) =>
            Typechecker_wrap_bc(T_O, T_N, T_O.inferArith1(Joint.def.core.UnaryOp.Neg(), e1, effs_O), T_N.inferArith1(Joint.def.core.UnaryOp.Neg(), e1, effs_N));
            assert T_N.infer(e_N, effs_N) == Result_forward((x: (Old.validation.types.Type,Old.validation.typechecker.Effects)) => (Type_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.Type,New.validation.typechecker.Effects)) => (Type_backward(x.0), Effects_backward(x.1)), T_O.wrap(Typechecker_inferArith1_bc(T_O, T_N, Joint.def.core.UnaryOp.Neg(), e1, effs_O, Joint.def.core.UnaryOp.Neg(), e1, effs_N);
            T_O.inferArith1(Joint.def.core.UnaryOp.Neg(), e1, effs_O)));
          case UnaryApp(MulBy(i), e1) =>
            Typechecker_wrap_bc(T_O, T_N, T_O.inferArith1(Joint.def.core.UnaryOp.MulBy(i), e1, effs_O), T_N.inferArith1(Joint.def.core.UnaryOp.MulBy(i), e1, effs_N));
            assert T_N.infer(e_N, effs_N) == Result_forward((x: (Old.validation.types.Type,Old.validation.typechecker.Effects)) => (Type_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.Type,New.validation.typechecker.Effects)) => (Type_backward(x.0), Effects_backward(x.1)), T_O.wrap(Typechecker_inferArith1_bc(T_O, T_N, Joint.def.core.UnaryOp.MulBy(i), e1, effs_O, Joint.def.core.UnaryOp.MulBy(i), e1, effs_N);
            T_O.inferArith1(Joint.def.core.UnaryOp.MulBy(i), e1, effs_O)));
          case UnaryApp(Like(p), e1) =>
            Typechecker_wrap_bc(T_O, T_N, T_O.inferLike(p, e1, effs_O), T_N.inferLike(p, e1, effs_N));
            assert T_N.infer(e_N, effs_N) == Result_forward((x: (Old.validation.types.Type,Old.validation.typechecker.Effects)) => (Type_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.Type,New.validation.typechecker.Effects)) => (Type_backward(x.0), Effects_backward(x.1)), T_O.wrap(Typechecker_inferLike_bc(T_O, T_N, p, e1, effs_O, p, e1, effs_N);
            T_O.inferLike(p, e1, effs_O)));
          case BinaryApp(Eq(), e1, e2) =>
            Typechecker_wrap_bc(T_O, T_N, T_O.inferEq(e1, e2, effs_O), T_N.inferEq(e1, e2, effs_N));
            assert T_N.infer(e_N, effs_N) == Result_forward((x: (Old.validation.types.Type,Old.validation.typechecker.Effects)) => (Type_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.Type,New.validation.typechecker.Effects)) => (Type_backward(x.0), Effects_backward(x.1)), T_O.wrap(Typechecker_inferEq_bc(T_O, T_N, e1, e2, effs_O, e1, e2, effs_N);
            T_O.inferEq(e1, e2, effs_O)));
          case BinaryApp(Less(), e1, e2) =>
            Typechecker_wrap_bc(T_O, T_N, T_O.inferIneq(Joint.def.core.BinaryOp.Less(), e1, e2, effs_O), T_N.inferIneq(Joint.def.core.BinaryOp.Less(), e1, e2, effs_N));
            assert T_N.infer(e_N, effs_N) == Result_forward((x: (Old.validation.types.Type,Old.validation.typechecker.Effects)) => (Type_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.Type,New.validation.typechecker.Effects)) => (Type_backward(x.0), Effects_backward(x.1)), T_O.wrap(Typechecker_inferIneq_bc(T_O, T_N, Joint.def.core.BinaryOp.Less(), e1, e2, effs_O, Joint.def.core.BinaryOp.Less(), e1, e2, effs_N);
            T_O.inferIneq(Joint.def.core.BinaryOp.Less(), e1, e2, effs_O)));
          case BinaryApp(LessEq(), e1, e2) =>
            Typechecker_wrap_bc(T_O, T_N, T_O.inferIneq(Joint.def.core.BinaryOp.LessEq(), e1, e2, effs_O), T_N.inferIneq(Joint.def.core.BinaryOp.LessEq(), e1, e2, effs_N));
            assert T_N.infer(e_N, effs_N) == Result_forward((x: (Old.validation.types.Type,Old.validation.typechecker.Effects)) => (Type_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.Type,New.validation.typechecker.Effects)) => (Type_backward(x.0), Effects_backward(x.1)), T_O.wrap(Typechecker_inferIneq_bc(T_O, T_N, Joint.def.core.BinaryOp.LessEq(), e1, e2, effs_O, Joint.def.core.BinaryOp.LessEq(), e1, e2, effs_N);
            T_O.inferIneq(Joint.def.core.BinaryOp.LessEq(), e1, e2, effs_O)));
          case BinaryApp(In(), e1, e2) =>
            Typechecker_wrap_bc(T_O, T_N, T_O.inferIn(e_O, e1, e2, effs_O), T_N.inferIn(e_N, e1, e2, effs_N));
            assert T_N.infer(e_N, effs_N) == Result_forward((x: (Old.validation.types.Type,Old.validation.typechecker.Effects)) => (Type_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.Type,New.validation.typechecker.Effects)) => (Type_backward(x.0), Effects_backward(x.1)), T_O.wrap(Typechecker_inferIn_bc(T_O, T_N, e_O, e1, e2, effs_O, e_N, e1, e2, effs_N);
            T_O.inferIn(e_O, e1, e2, effs_O)));
          case BinaryApp(Add(), e1, e2) =>
            Typechecker_wrap_bc(T_O, T_N, T_O.inferArith2(Joint.def.core.BinaryOp.Add(), e1, e2, effs_O), T_N.inferArith2(Joint.def.core.BinaryOp.Add(), e1, e2, effs_N));
            assert T_N.infer(e_N, effs_N) == Result_forward((x: (Old.validation.types.Type,Old.validation.typechecker.Effects)) => (Type_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.Type,New.validation.typechecker.Effects)) => (Type_backward(x.0), Effects_backward(x.1)), T_O.wrap(Typechecker_inferArith2_bc(T_O, T_N, Joint.def.core.BinaryOp.Add(), e1, e2, effs_O, Joint.def.core.BinaryOp.Add(), e1, e2, effs_N);
            T_O.inferArith2(Joint.def.core.BinaryOp.Add(), e1, e2, effs_O)));
          case BinaryApp(Sub(), e1, e2) =>
            Typechecker_wrap_bc(T_O, T_N, T_O.inferArith2(Joint.def.core.BinaryOp.Sub(), e1, e2, effs_O), T_N.inferArith2(Joint.def.core.BinaryOp.Sub(), e1, e2, effs_N));
            assert T_N.infer(e_N, effs_N) == Result_forward((x: (Old.validation.types.Type,Old.validation.typechecker.Effects)) => (Type_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.Type,New.validation.typechecker.Effects)) => (Type_backward(x.0), Effects_backward(x.1)), T_O.wrap(Typechecker_inferArith2_bc(T_O, T_N, Joint.def.core.BinaryOp.Sub(), e1, e2, effs_O, Joint.def.core.BinaryOp.Sub(), e1, e2, effs_N);
            T_O.inferArith2(Joint.def.core.BinaryOp.Sub(), e1, e2, effs_O)));
          case BinaryApp(ContainsAny(), e1, e2) =>
            Typechecker_wrap_bc(T_O, T_N, T_O.inferContainsAnyAll(Joint.def.core.BinaryOp.ContainsAny(), e1, e2, effs_O), T_N.inferContainsAnyAll(Joint.def.core.BinaryOp.ContainsAny(), e1, e2, effs_N));
            assert T_N.infer(e_N, effs_N) == Result_forward((x: (Old.validation.types.Type,Old.validation.typechecker.Effects)) => (Type_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.Type,New.validation.typechecker.Effects)) => (Type_backward(x.0), Effects_backward(x.1)), T_O.wrap(Typechecker_inferContainsAnyAll_bc(T_O, T_N, Joint.def.core.BinaryOp.ContainsAny(), e1, e2, effs_O, Joint.def.core.BinaryOp.ContainsAny(), e1, e2, effs_N);
            T_O.inferContainsAnyAll(Joint.def.core.BinaryOp.ContainsAny(), e1, e2, effs_O)));
          case BinaryApp(ContainsAll(), e1, e2) =>
            Typechecker_wrap_bc(T_O, T_N, T_O.inferContainsAnyAll(Joint.def.core.BinaryOp.ContainsAll(), e1, e2, effs_O), T_N.inferContainsAnyAll(Joint.def.core.BinaryOp.ContainsAll(), e1, e2, effs_N));
            assert T_N.infer(e_N, effs_N) == Result_forward((x: (Old.validation.types.Type,Old.validation.typechecker.Effects)) => (Type_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.Type,New.validation.typechecker.Effects)) => (Type_backward(x.0), Effects_backward(x.1)), T_O.wrap(Typechecker_inferContainsAnyAll_bc(T_O, T_N, Joint.def.core.BinaryOp.ContainsAll(), e1, e2, effs_O, Joint.def.core.BinaryOp.ContainsAll(), e1, e2, effs_N);
            T_O.inferContainsAnyAll(Joint.def.core.BinaryOp.ContainsAll(), e1, e2, effs_O)));
          case BinaryApp(Contains(), e1, e2) =>
            Typechecker_wrap_bc(T_O, T_N, T_O.inferContains(e1, e2, effs_O), T_N.inferContains(e1, e2, effs_N));
            assert T_N.infer(e_N, effs_N) == Result_forward((x: (Old.validation.types.Type,Old.validation.typechecker.Effects)) => (Type_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.Type,New.validation.typechecker.Effects)) => (Type_backward(x.0), Effects_backward(x.1)), T_O.wrap(Typechecker_inferContains_bc(T_O, T_N, e1, e2, effs_O, e1, e2, effs_N);
            T_O.inferContains(e1, e2, effs_O)));
          case Record(r) =>
            assert T_N.infer(e_N, effs_N) == Result_forward((x: (Old.validation.types.Type,Old.validation.typechecker.Effects)) => (Type_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.Type,New.validation.typechecker.Effects)) => (Type_backward(x.0), Effects_backward(x.1)), var rt :- (Typechecker_inferRecord_bc(T_O, T_N, Joint.def.core.Expr.Record(r), r, effs_O, Joint.def.core.Expr.Record(r), r, effs_N);
            T_O.inferRecord(Joint.def.core.Expr.Record(r), r, effs_O));
            Typechecker_wrap_bc(T_O, T_N, Old.validation.types.Ok(Old.validation.types.Type.Record(rt)), New.validation.types.Ok(New.validation.types.Type.Record(RecordType_forward(rt))));
            T_O.wrap(Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Record(rt), New.validation.types.Type.Record(RecordType_forward(rt)));
            Old.validation.types.Ok(Old.validation.types.Type.Record(rt))));
          case Set(es) =>
            assert T_N.infer(e_N, effs_N) == Result_forward((x: (Old.validation.types.Type,Old.validation.typechecker.Effects)) => (Type_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.Type,New.validation.typechecker.Effects)) => (Type_backward(x.0), Effects_backward(x.1)), var st :- (Typechecker_inferSet_bc(T_O, T_N, e_O, es, effs_O, e_N, es, effs_N);
            T_O.inferSet(e_O, es, effs_O));
            Typechecker_wrap_bc(T_O, T_N, Old.validation.types.Ok(Old.validation.types.Type.Set(st)), New.validation.types.Ok(New.validation.types.Type.Set(Type_forward(st))));
            T_O.wrap(Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.types.Type.Set(st), New.validation.types.Type.Set(Type_forward(st)));
            Old.validation.types.Ok(Old.validation.types.Type.Set(st))));
          case HasAttr(e1, k) =>
            Typechecker_inferHasAttr_bc(T_O, T_N, e1, k, effs_O, e1, k, effs_N);
            assert T_N.infer(e_N, effs_N) == Result_forward((x: (Old.validation.types.Type,Old.validation.typechecker.Effects)) => (Type_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.Type,New.validation.typechecker.Effects)) => (Type_backward(x.0), Effects_backward(x.1)), T_O.inferHasAttr(e1, k, effs_O));
          case GetAttr(e1, k) =>
            Typechecker_wrap_bc(T_O, T_N, T_O.inferGetAttr(e1, k, effs_O), T_N.inferGetAttr(e1, k, effs_N));
            assert T_N.infer(e_N, effs_N) == Result_forward((x: (Old.validation.types.Type,Old.validation.typechecker.Effects)) => (Type_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.Type,New.validation.typechecker.Effects)) => (Type_backward(x.0), Effects_backward(x.1)), T_O.wrap(Typechecker_inferGetAttr_bc(T_O, T_N, e1, k, effs_O, e1, k, effs_N);
            T_O.inferGetAttr(e1, k, effs_O)));
          case Call(name, args) =>
            Typechecker_wrap_bc(T_O, T_N, T_O.inferCall(e_O, name, args, effs_O), T_N.inferCall(e_N, name, args, effs_N));
            assert T_N.infer(e_N, effs_N) == Result_forward((x: (Old.validation.types.Type,Old.validation.typechecker.Effects)) => (Type_forward(x.0), Effects_forward(x.1)), (x: (New.validation.types.Type,New.validation.typechecker.Effects)) => (Type_backward(x.0), Effects_backward(x.1)), T_O.wrap(Typechecker_inferCall_bc(T_O, T_N, e_O, name, args, effs_O, e_N, name, args, effs_N);
            T_O.inferCall(e_O, name, args, effs_O)));
        }
      }

      lemma Typechecker_typecheck_bc(T_O: Old.validation.typechecker.Typechecker, T_N: New.validation.typechecker.Typechecker, e_O: Joint.def.core.Expr, t_O: Old.validation.types.Type, e_N: Joint.def.core.Expr, t_N: New.validation.types.Type)
        decreases T_O, e_O, t_O
        requires T_N == Typechecker_forward(T_O)
        requires e_N == e_O
        requires t_N == Type_forward(t_O)
        ensures T_N.typecheck(e_N, t_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), T_O.typecheck(e_O, t_O))
      {
        assert T_N.typecheck(e_N, t_N) == Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), var (t1, _) :- (Typechecker_infer_bc(T_O, T_N, e_O, Old.validation.typechecker.Effects.empty(), e_N, New.validation.typechecker.Effects.empty());
        T_O.infer(e_O, Effects_empty_bc();
        Old.validation.typechecker.Effects.empty()));
        var _ :- (Typechecker_ensureSubty_bc(T_O, T_N, t1, t_O, Type_forward(t1), t_N);
        T_O.ensureSubty(t1, t_O));
        Ok_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), t1, Type_forward(t1));
        Old.validation.types.Ok(t1));
      }
    }

    module ext {
      import Joint

      import Old

      import New

      import Translations

      lemma register_bc()
        ensures New.validation.ext.register() == Translations.MapBuiltinTypes.Map((mp: Joint.def.base.Name) => mp, (mp: Joint.def.base.Name) => mp, (mp: Old.validation.types.ExtFunType) => ExtFunType_forward(mp), Old.validation.ext.register())
      {
        assert New.validation.ext.register() == Translations.MapBuiltinTypes.Map((mp: Joint.def.base.Name) => mp, (mp: Joint.def.base.Name) => mp, (mp: Old.validation.types.ExtFunType) => ExtFunType_forward(mp), (decimal.register_bc();
        Old.validation.ext.decimal.register()) + (ipaddr.register_bc();
        Old.validation.ext.ipaddr.register()));
      }

      lemma {:axiom} extFunTypes_bc()
        ensures Translations.MapBuiltinTypes.Map((mp: Joint.def.base.Name) => mp, (mp: Joint.def.base.Name) => mp, (mp: Old.validation.types.ExtFunType) => ExtFunType_forward(mp), Old.validation.ext.extFunTypes) == New.validation.ext.extFunTypes

      import opened def.base

      import opened types

      module decimal {
        import Joint

        import Old

        import New

        import Translations

        lemma register_bc()
          ensures New.validation.ext.decimal.register() == Translations.MapBuiltinTypes.Map((mp: Joint.def.base.Name) => mp, (mp: Joint.def.base.Name) => mp, (mp: Old.validation.types.ExtFunType) => ExtFunType_forward(mp), Old.validation.ext.decimal.register())
        {
          var D := Old.validation.types.Type.Extension(Joint.def.base.Name.fromStr("decimal")); assert New.validation.ext.decimal.register() == Translations.MapBuiltinTypes.Map((mp: Joint.def.base.Name) => mp, (mp: Joint.def.base.Name) => mp, (mp: Old.validation.types.ExtFunType) => ExtFunType_forward(mp), map [Joint.def.base.Name.fromStr("decimal") := Old.validation.types.ExtFunType.ExtFunType([Old.validation.types.Type.String()], D, Joint.def.std.Option.Some(Old.validation.ext.decimal.checkDecimalArgs)) , Joint.def.base.Name.fromStr("lessThan") := Old.validation.types.ExtFunType.ExtFunType([D, D], Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool()), Joint.def.std.Option.None()) , Joint.def.base.Name.fromStr("lessThanOrEqual") := Old.validation.types.ExtFunType.ExtFunType([D, D], Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool()), Joint.def.std.Option.None()) , Joint.def.base.Name.fromStr("greaterThan") := Old.validation.types.ExtFunType.ExtFunType([D, D], Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool()), Joint.def.std.Option.None()) , Joint.def.base.Name.fromStr("greaterThanOrEqual") := Old.validation.types.ExtFunType.ExtFunType([D, D], Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool()), Joint.def.std.Option.None())]);
        }

        lemma checkDecimalArgs_bc(args_O: seq<Joint.def.core.Expr>, args_N: seq<Joint.def.core.Expr>)
          decreases args_O
          requires args_N == args_O
          ensures New.validation.ext.decimal.checkDecimalArgs(args_N) == types.Result_forward((x: ()) => (), (x: ()) => (), Old.validation.ext.decimal.checkDecimalArgs(args_O))
        {
          if (|args_O| != 1) {
            assert New.validation.ext.decimal.checkDecimalArgs(args_N) == types.Result_forward((x: ()) => (), (x: ()) => (), Joint.def.std.Result.Ok(()));
          } else {
            match args_O[0] {
              case PrimitiveLit(String(s)) =>
                match Joint.def.ext.decimal.parseDecimal.Parse(s) {
                  case None() =>
                    assert New.validation.ext.decimal.checkDecimalArgs(args_N) == types.Result_forward((x: ()) => (), (x: ()) => (), Joint.def.std.Result.Err(Old.validation.types.TypeError.ExtensionErr(Joint.def.core.Expr.Call(Joint.def.base.Name.fromStr("decimal"), args_O))));
                  case Some(_) =>
                    assert New.validation.ext.decimal.checkDecimalArgs(args_N) == types.Result_forward((x: ()) => (), (x: ()) => (), Joint.def.std.Result.Ok(()));
                }
              case _ =>
                assert New.validation.ext.decimal.checkDecimalArgs(args_N) == types.Result_forward((x: ()) => (), (x: ()) => (), Joint.def.std.Result.Ok(()));
            }
          }
        }

        import opened def.std

        import opened def.base

        import opened def.core

        import opened def.ext.decimal.parseDecimal

        import opened types
      }

      module ipaddr {
        import Joint

        import Old

        import New

        import Translations

        lemma register_bc()
          ensures New.validation.ext.ipaddr.register() == Translations.MapBuiltinTypes.Map((mp: Joint.def.base.Name) => mp, (mp: Joint.def.base.Name) => mp, (mp: Old.validation.types.ExtFunType) => ExtFunType_forward(mp), Old.validation.ext.ipaddr.register())
        {
          var I := Old.validation.types.Type.Extension(Joint.def.base.Name.fromStr("ipaddr")); assert New.validation.ext.ipaddr.register() == Translations.MapBuiltinTypes.Map((mp: Joint.def.base.Name) => mp, (mp: Joint.def.base.Name) => mp, (mp: Old.validation.types.ExtFunType) => ExtFunType_forward(mp), map [Joint.def.base.Name.fromStr("ip") := Old.validation.types.ExtFunType.ExtFunType([Old.validation.types.Type.String()], I, Joint.def.std.Option.Some(Old.validation.ext.ipaddr.checkIpArgs)) , Joint.def.base.Name.fromStr("isIpv4") := Old.validation.types.ExtFunType.ExtFunType([I], Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool()), Joint.def.std.Option.None()) , Joint.def.base.Name.fromStr("isIpv6") := Old.validation.types.ExtFunType.ExtFunType([I], Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool()), Joint.def.std.Option.None()) , Joint.def.base.Name.fromStr("isLoopback") := Old.validation.types.ExtFunType.ExtFunType([I], Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool()), Joint.def.std.Option.None()) , Joint.def.base.Name.fromStr("isMulticast") := Old.validation.types.ExtFunType.ExtFunType([I], Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool()), Joint.def.std.Option.None()) , Joint.def.base.Name.fromStr("isInRange") := Old.validation.types.ExtFunType.ExtFunType([I, I], Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool()), Joint.def.std.Option.None())]);
        }

        lemma checkIpArgs_bc(args_O: seq<Joint.def.core.Expr>, args_N: seq<Joint.def.core.Expr>)
          decreases args_O
          requires args_N == args_O
          ensures New.validation.ext.ipaddr.checkIpArgs(args_N) == types.Result_forward((x: ()) => (), (x: ()) => (), Old.validation.ext.ipaddr.checkIpArgs(args_O))
        {
          if (|args_O| != 1) {
            assert New.validation.ext.ipaddr.checkIpArgs(args_N) == types.Result_forward((x: ()) => (), (x: ()) => (), Joint.def.std.Result.Ok(()));
          } else {
            match args_O[0] {
              case PrimitiveLit(String(s)) =>
                match Joint.def.ext.ipaddr.parseIPAddr.parse(s) {
                  case None() =>
                    assert New.validation.ext.ipaddr.checkIpArgs(args_N) == types.Result_forward((x: ()) => (), (x: ()) => (), Joint.def.std.Result.Err(Old.validation.types.TypeError.ExtensionErr(Joint.def.core.Expr.Call(Joint.def.base.Name.fromStr("ip"), args_O))));
                  case Some(_) =>
                    assert New.validation.ext.ipaddr.checkIpArgs(args_N) == types.Result_forward((x: ()) => (), (x: ()) => (), Joint.def.std.Result.Ok(()));
                }
              case _ =>
                assert New.validation.ext.ipaddr.checkIpArgs(args_N) == types.Result_forward((x: ()) => (), (x: ()) => (), Joint.def.std.Result.Ok(()));
            }
          }
        }

        import opened def.std

        import opened def.base

        import opened def.core

        import opened def.ext.ipaddr.parseIPAddr

        import opened types
      }
    }

    module strict {
      import Old
      import New
      import opened types
      function StrictTypeError_to_TypeError(x: Old.validation.strict.StrictTypeError): New.validation.types.TypeError
      {
        match x {
          case TypeError(t) => TypeError_forward(t)
          case _ => assume false; New.validation.types.EmptyLUB()
        }
      }
      function Result_forward<T_O, T_N>(T_forward: T_O->T_N, T_backward: T_N->T_O, R_O: Old.validation.strict.Result<T_O>): New.validation.types.Result<T_N>
      {
        R_O.MapErr(StrictTypeError_to_TypeError).Map(T_forward)
      }
    }

    module validator {
      import Joint

      import Old

      import New

      import Translations

      import opened def.base

      import opened def.core

      import opened typechecker

      import opened types

      import opened util

      import strict

      function Schema_forward(S_O: Old.validation.validator.Schema): New.validation.validator.Schema
      {
        match S_O {
          case Schema(entityTypes_O, actionIds_O) =>
            /* unchanged constructor */ New.validation.validator.Schema.Schema(Translations.MapBuiltinTypes.Map((mp: Joint.def.core.EntityType) => mp, (mp: Joint.def.core.EntityType) => mp, (mp: Old.validation.validator.TypecheckerEntityType) => TypecheckerEntityType_forward(mp), entityTypes_O), Translations.MapBuiltinTypes.Map((mp: Joint.def.core.EntityUID) => mp, (mp: Joint.def.core.EntityUID) => mp, (mp: Old.validation.validator.TypecheckerActionId) => TypecheckerActionId_forward(mp), actionIds_O))
        }
      }

      function Schema_backward(S_N: New.validation.validator.Schema): Old.validation.validator.Schema
      {
        match S_N {
          case Schema(entityTypes_N, actionIds_N) =>
            /* unchanged constructor */ Old.validation.validator.Schema.Schema(Translations.MapBuiltinTypes.Map((mp: Joint.def.core.EntityType) => mp, (mp: Joint.def.core.EntityType) => mp, (mp: New.validation.validator.TypecheckerEntityType) => TypecheckerEntityType_backward(mp), entityTypes_N), Translations.MapBuiltinTypes.Map((mp: Joint.def.core.EntityUID) => mp, (mp: Joint.def.core.EntityUID) => mp, (mp: New.validation.validator.TypecheckerActionId) => TypecheckerActionId_backward(mp), actionIds_N))
        }
      }

      lemma Schema_allRequestTypes_bc(S_O: Old.validation.validator.Schema, S_N: New.validation.validator.Schema)
        decreases S_O
        requires S_N == Schema_forward(S_O)
        ensures S_N.allRequestTypes() == Translations.MapBuiltinTypes.Set((st: Old.validation.typechecker.RequestType) => RequestType_forward(st), S_O.allRequestTypes())
      {
        assert S_N.allRequestTypes() == Translations.MapBuiltinTypes.Set((st: Old.validation.typechecker.RequestType) => RequestType_forward(st), set a: Joint.def.core.EntityUID, p: Old.validation.types.Option<Joint.def.core.EntityType>, r: Old.validation.types.Option<Joint.def.core.EntityType> | a in S_O.actionIds.Keys && p in S_O.actionIds[a].appliesTo.principalApplySpec && r in S_O.actionIds[a].appliesTo.resourceApplySpec :: Old.validation.typechecker.RequestType.RequestType(p, a, r, Old.validation.types.RecordType.RecordType(S_O.actionIds[a].context, Old.validation.types.AttrsTag.ClosedAttributes())));
      }

      lemma Schema_makeEntityTypeStore_bc(S_O: Old.validation.validator.Schema, S_N: New.validation.validator.Schema)
        decreases S_O
        requires S_N == Schema_forward(S_O)
        ensures S_N.makeEntityTypeStore() == EntityTypeStore_forward(S_O.makeEntityTypeStore())
      {
        var types := map et: Joint.def.core.EntityType | et in S_O.entityTypes :: Old.validation.types.RecordType.RecordType(S_O.entityTypes[et].attributes, Old.validation.types.AttrsTag.ClosedAttributes()); var descendants := map et: Joint.def.core.EntityType | et in S_O.entityTypes :: S_O.entityTypes[et].descendants; assert S_N.makeEntityTypeStore() == EntityTypeStore_forward(Old.validation.typechecker.EntityTypeStore.EntityTypeStore(types, descendants));
      }

      lemma Schema_makeActionStore_bc(S_O: Old.validation.validator.Schema, S_N: New.validation.validator.Schema)
        decreases S_O
        requires S_N == Schema_forward(S_O)
        ensures S_N.makeActionStore() == ActionStore_forward(S_O.makeActionStore())
      {
        var descendants := map act: Joint.def.core.EntityUID | act in S_O.actionIds :: S_O.actionIds[act].descendants; assert S_N.makeActionStore() == ActionStore_forward(Old.validation.typechecker.ActionStore.ActionStore(descendants));
      }

      function TypecheckerEntityType_forward(T_O: Old.validation.validator.TypecheckerEntityType): New.validation.validator.TypecheckerEntityType
      {
        match T_O {
          case TypecheckerEntityType(descendants_O, attributes_O) =>
            /* unchanged constructor */ New.validation.validator.TypecheckerEntityType.TypecheckerEntityType(descendants_O, Translations.MapBuiltinTypes.Map((mp: Joint.def.core.Attr) => mp, (mp: Joint.def.core.Attr) => mp, (mp: Old.validation.types.AttrType) => AttrType_forward(mp), attributes_O))
        }
      }

      function TypecheckerEntityType_backward(T_N: New.validation.validator.TypecheckerEntityType): Old.validation.validator.TypecheckerEntityType
      {
        match T_N {
          case TypecheckerEntityType(descendants_N, attributes_N) =>
            /* unchanged constructor */ Old.validation.validator.TypecheckerEntityType.TypecheckerEntityType(descendants_N, Translations.MapBuiltinTypes.Map((mp: Joint.def.core.Attr) => mp, (mp: Joint.def.core.Attr) => mp, (mp: New.validation.types.AttrType) => AttrType_backward(mp), attributes_N))
        }
      }

      function TypecheckerActionId_forward(T_O: Old.validation.validator.TypecheckerActionId): New.validation.validator.TypecheckerActionId
      {
        match T_O {
          case TypecheckerActionId(appliesTo_O, descendants_O, context_O) =>
            /* unchanged constructor */ New.validation.validator.TypecheckerActionId.TypecheckerActionId(TypecheckerApplySpec_forward(appliesTo_O), descendants_O, Translations.MapBuiltinTypes.Map((mp: Joint.def.core.Attr) => mp, (mp: Joint.def.core.Attr) => mp, (mp: Old.validation.types.AttrType) => AttrType_forward(mp), context_O))
        }
      }

      function TypecheckerActionId_backward(T_N: New.validation.validator.TypecheckerActionId): Old.validation.validator.TypecheckerActionId
      {
        match T_N {
          case TypecheckerActionId(appliesTo_N, descendants_N, context_N) =>
            /* unchanged constructor */ Old.validation.validator.TypecheckerActionId.TypecheckerActionId(TypecheckerApplySpec_backward(appliesTo_N), descendants_N, Translations.MapBuiltinTypes.Map((mp: Joint.def.core.Attr) => mp, (mp: Joint.def.core.Attr) => mp, (mp: New.validation.types.AttrType) => AttrType_backward(mp), context_N))
        }
      }

      function TypecheckerApplySpec_forward(T_O: Old.validation.validator.TypecheckerApplySpec): New.validation.validator.TypecheckerApplySpec
      {
        match T_O {
          case TypecheckerApplySpec(principalApplySpec_O, resourceApplySpec_O) =>
            /* unchanged constructor */ New.validation.validator.TypecheckerApplySpec.TypecheckerApplySpec(Translations.MapBuiltinTypes.Set((st: Old.validation.types.Option<Joint.def.core.EntityType>) => Option_forward((x: Joint.def.core.EntityType) => x, (x: Joint.def.core.EntityType) => x, st), principalApplySpec_O), Translations.MapBuiltinTypes.Set((st: Old.validation.types.Option<Joint.def.core.EntityType>) => Option_forward((x: Joint.def.core.EntityType) => x, (x: Joint.def.core.EntityType) => x, st), resourceApplySpec_O))
        }
      }

      function TypecheckerApplySpec_backward(T_N: New.validation.validator.TypecheckerApplySpec): Old.validation.validator.TypecheckerApplySpec
      {
        match T_N {
          case TypecheckerApplySpec(principalApplySpec_N, resourceApplySpec_N) =>
            /* unchanged constructor */ Old.validation.validator.TypecheckerApplySpec.TypecheckerApplySpec(Translations.MapBuiltinTypes.Set((st: New.validation.types.Option<Joint.def.core.EntityType>) => Option_backward((x: Joint.def.core.EntityType) => x, (x: Joint.def.core.EntityType) => x, st), principalApplySpec_N), Translations.MapBuiltinTypes.Set((st: New.validation.types.Option<Joint.def.core.EntityType>) => Option_backward((x: Joint.def.core.EntityType) => x, (x: Joint.def.core.EntityType) => x, st), resourceApplySpec_N))
        }
      }

      function ValidationError_forward(V_O: Old.validation.validator.ValidationError): New.validation.validator.ValidationError
      {
        match V_O {
          case StrictTypeError(x0_O) =>
            /* deleted constructor */ Translations.Utils.???()
          case AllFalse() =>
            /* unchanged constructor */ New.validation.validator.ValidationError.AllFalse()
        }
      }

      function ValidationError_backward(V_N: New.validation.validator.ValidationError): Old.validation.validator.ValidationError
      {
        match V_N {
          case AllFalse() =>
            /* unchanged constructor */ Old.validation.validator.ValidationError.AllFalse()
          case TypeError(x0_N) =>
            /* deleted constructor */ Translations.Utils.???()
        }
      }

      function ValidationMode_forward(V_O: Old.validation.validator.ValidationMode): New.validation.types.ValidationMode
      {
        match V_O {
          case Permissive() => New.validation.types.Permissive()
          case Strict() => New.validation.types.Strict()
        }
      }

      function ValidationMode_backward(V_N: New.validation.types.ValidationMode): Old.validation.validator.ValidationMode
      {
        match V_N {
          case Permissive() => Old.validation.validator.Permissive()
          case Strict() => Old.validation.validator.Strict()
        }
      }

      function Validator_forward(V_O: Old.validation.validator.Validator): New.validation.validator.Validator
      {
        match V_O {
          case Validator(schema_O, mode_O) =>
            /* added/deleted/updated constructor arguments */ New.validation.validator.Validator.Validator(Schema_forward(schema_O), ValidationMode_forward(mode_O))
        }
      }

      function Validator_backward(V_N: New.validation.validator.Validator): Old.validation.validator.Validator
      {
        match V_N {
          case Validator(schema_N, mode_N) =>
            /* added/deleted/updated constructor arguments */ Old.validation.validator.Validator.Validator(Schema_backward(schema_N), ValidationMode_backward(mode_N))
        }
      }

      function TypeError_back_to_StrictTypeError(x: New.validation.types.TypeError): Old.validation.strict.StrictTypeError
      {
        Old.validation.strict.TypeError(TypeError_backward(x))
      }

      lemma Validator_Typecheck_bc(V_O: Old.validation.validator.Validator, V_N: New.validation.validator.Validator, e_O: Joint.def.core.Expr, ets_O: Old.validation.typechecker.EntityTypeStore, acts_O: Old.validation.typechecker.ActionStore, reqty_O: Old.validation.typechecker.RequestType, e_N: Joint.def.core.Expr, ets_N: New.validation.typechecker.EntityTypeStore, acts_N: New.validation.typechecker.ActionStore, reqty_N: New.validation.typechecker.RequestType)
        decreases V_O, e_O, ets_O, acts_O, reqty_O
        requires V_N == Validator_forward(V_O)
        requires e_N == e_O
        requires ets_N == EntityTypeStore_forward(ets_O)
        requires acts_N == ActionStore_forward(acts_O)
        requires reqty_N == RequestType_forward(reqty_O)
        ensures V_N.Typecheck(e_N, ets_N, acts_N, reqty_N) == std.Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), (x: Old.validation.strict.StrictTypeError) => strict.StrictTypeError_to_TypeError(x), (x: New.validation.types.TypeError) => TypeError_back_to_StrictTypeError(x), V_O.Typecheck(e_O, ets_O, acts_O, reqty_O))
      {
        if (V_O.mode.Permissive?) {
          match Old.validation.typechecker.Typechecker.Typechecker(ets_O, acts_O, reqty_O).typecheck(e_O, Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool())) {
            case Ok(ty) =>
              assert V_N.Typecheck(e_N, ets_N, acts_N, reqty_N) == std.Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), (x: Old.validation.strict.StrictTypeError) => strict.StrictTypeError_to_TypeError(x), (x: New.validation.types.TypeError) => TypeError_back_to_StrictTypeError(x), Joint.def.std.Result.Ok(ty));
            case Err(er) =>
              assert V_N.Typecheck(e_N, ets_N, acts_N, reqty_N) == std.Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), (x: Old.validation.strict.StrictTypeError) => strict.StrictTypeError_to_TypeError(x), (x: New.validation.types.TypeError) => TypeError_back_to_StrictTypeError(x), Joint.def.std.Result.Err(Old.validation.strict.StrictTypeError.TypeError(er)));
          }
        } else {
          assert V_N.Typecheck(e_N, ets_N, acts_N, reqty_N) == std.Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), (x: Old.validation.strict.StrictTypeError) => strict.StrictTypeError_to_TypeError(x), (x: New.validation.types.TypeError) => TypeError_back_to_StrictTypeError(x), Old.validation.strict.StrictTypechecker.StrictTypechecker(ets_O, acts_O, reqty_O).typecheck(e_O, Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool())));
        }
      }
    }

    module thm {
      import Joint

      import Old

      import New

      import Translations

      module base {
        import Joint

        import Old

        import New

        import Translations

        lemma {:axiom} Evaluate_bc(e_O: Joint.def.core.Expr, r_O: Joint.def.core.Request, s_O: Joint.def.core.EntityStore, e_N: Joint.def.core.Expr, r_N: Joint.def.core.Request, s_N: Joint.def.core.EntityStore)
          decreases e_O, r_O, s_O
          requires e_N == e_O
          requires r_N == r_O
          requires s_N == s_O
          ensures New.validation.thm.base.Evaluate(e_N, r_N, s_N) == Old.validation.thm.base.Evaluate(e_O, r_O, s_O)

        lemma {:axiom} unspecifiedPrincipalEuid_bc()
          ensures Old.validation.thm.base.unspecifiedPrincipalEuid == New.validation.thm.base.unspecifiedPrincipalEuid

        lemma {:axiom} unspecifiedResourceEuid_bc()
          ensures Old.validation.thm.base.unspecifiedResourceEuid == New.validation.thm.base.unspecifiedResourceEuid

        lemma InstanceOfRequestType_bc(r_O: Joint.def.core.Request, reqty_O: Old.validation.typechecker.RequestType, r_N: Joint.def.core.Request, reqty_N: New.validation.typechecker.RequestType)
          decreases r_O, reqty_O
          requires r_N == r_O
          requires reqty_N == RequestType_forward(reqty_O)
          ensures New.validation.thm.base.InstanceOfRequestType(r_N, reqty_N) == Old.validation.thm.base.InstanceOfRequestType(r_O, reqty_O)
        {
          assert New.validation.thm.base.InstanceOfRequestType(r_N, reqty_N) == (match reqty_O.principal {
            case None() =>
              r_O.principal == Old.validation.thm.base.unspecifiedPrincipalEuid
            case Some(pt) =>
              InstanceOfEntityType_bc(r_O.principal, pt, r_N.principal, pt);
              Old.validation.thm.base.InstanceOfEntityType(r_O.principal, pt)
          } && r_O.action == reqty_O.action && match reqty_O.resource {
            case None() =>
              r_O.resource == Old.validation.thm.base.unspecifiedResourceEuid
            case Some(rt) =>
              InstanceOfEntityType_bc(r_O.resource, rt, r_N.resource, rt);
              Old.validation.thm.base.InstanceOfEntityType(r_O.resource, rt)
          } && (InstanceOfRecordType_bc(r_O.context, reqty_O.context, r_N.context, reqty_N.context);
          Old.validation.thm.base.InstanceOfRecordType(r_O.context, reqty_O.context)));
        }

        lemma {:axiom} InstanceOfEntityType_bc(e_O: Joint.def.core.EntityUID, ety_O: Joint.def.core.EntityType, e_N: Joint.def.core.EntityUID, ety_N: Joint.def.core.EntityType)
          decreases e_O, ety_O
          requires e_N == e_O
          requires ety_N == ety_O
          ensures New.validation.thm.base.InstanceOfEntityType(e_N, ety_N) == Old.validation.thm.base.InstanceOfEntityType(e_O, ety_O)

        lemma InstanceOfRecordType_bc(r_O: Joint.def.core.Record, rt_O: Old.validation.types.RecordType, r_N: Joint.def.core.Record, rt_N: New.validation.types.RecordType)
          decreases r_O, rt_O
          requires r_N == r_O
          requires rt_N == RecordType_forward(rt_O)
          ensures New.validation.thm.base.InstanceOfRecordType(r_N, rt_N) == Old.validation.thm.base.InstanceOfRecordType(r_O, rt_O)
        {
          assert New.validation.thm.base.InstanceOfRecordType(r_N, rt_N) == ((forall k: string :: k in r_O ==>
            k in rt_O.attrs && (InstanceOfType_bc(r_O[k], rt_O.attrs[k].ty, r_N[k], rt_N.attrs[k].ty);
            Old.validation.thm.base.InstanceOfType(r_O[k], rt_O.attrs[k].ty))) && (forall k: string :: k in rt_O.attrs && rt_O.attrs[k].isRequired ==> k in r_O));
        }

        lemma InstanceOfEntityTypeStore_bc(s_O: Joint.def.core.EntityStore, ets_O: Old.validation.typechecker.EntityTypeStore, s_N: Joint.def.core.EntityStore, ets_N: New.validation.typechecker.EntityTypeStore)
          decreases s_O, ets_O
          requires s_N == s_O
          requires ets_N == EntityTypeStore_forward(ets_O)
          ensures New.validation.thm.base.InstanceOfEntityTypeStore(s_N, ets_N) == Old.validation.thm.base.InstanceOfEntityTypeStore(s_O, ets_O)
        {
          if (forall e: Joint.def.core.EntityUID :: e in s_O.entities.Keys ==>
            (var ety := e.ty;
            var edata := s_O.entities[e];
            ety != Joint.def.core.EntityType.UNSPECIFIED && ety in ets_O.types && (InstanceOfRecordType_bc(edata.attrs, ets_O.types[ety], edata.attrs, ets_N.types[ety]);
            Old.validation.thm.base.InstanceOfRecordType(edata.attrs, ets_O.types[ety])) && (forall p: Joint.def.core.EntityUID :: p in edata.ancestors ==> p.ty in ets_O.descendants && ety in ets_O.descendants[p.ty]))) {
            forall e: Joint.def.core.EntityUID | e in s_O.entities.Keys
              ensures var ety := e.ty;
              var edata := s_N.entities[e];
              ety != Joint.def.core.EntityType.UNSPECIFIED && ety in ets_N.types && New.validation.thm.base.InstanceOfRecordType(edata.attrs, ets_N.types[ety]) && (forall p: Joint.def.core.EntityUID :: p in edata.ancestors ==> p.ty in ets_N.descendants && ety in ets_N.descendants[p.ty]) {
              var ety := e.ty;
              var edata := s_O.entities[e];
              {
                InstanceOfRecordType_bc(edata.attrs, ets_O.types[ety], edata.attrs, ets_N.types[ety]);
                forall p: Joint.def.core.EntityUID | p in edata.ancestors {}
              }
            }
          } else {
            var e :| e in s_O.entities.Keys && !(var ety := e.ty;
            var edata := s_O.entities[e];
            ety != Joint.def.core.EntityType.UNSPECIFIED && ety in ets_O.types && (InstanceOfRecordType_bc(edata.attrs, ets_O.types[ety], edata.attrs, ets_N.types[ety]);
            Old.validation.thm.base.InstanceOfRecordType(edata.attrs, ets_O.types[ety])) && (forall p: Joint.def.core.EntityUID :: p in edata.ancestors ==> p.ty in ets_O.descendants && ety in ets_O.descendants[p.ty]));
            assert !(var ety := e.ty;
            var edata := s_N.entities[e];
            ety != Joint.def.core.EntityType.UNSPECIFIED && ety in ets_N.types && New.validation.thm.base.InstanceOfRecordType(edata.attrs, ets_N.types[ety]) && (forall p: Joint.def.core.EntityUID :: p in edata.ancestors ==> p.ty in ets_N.descendants && ety in ets_N.descendants[p.ty])) by {
              var ety := e.ty;
              var edata := s_O.entities[e];
              {
                InstanceOfRecordType_bc(edata.attrs, ets_O.types[ety], edata.attrs, ets_N.types[ety]);
                forall p: Joint.def.core.EntityUID | p in edata.ancestors {}
              }
            }
          }
        }

        lemma {:axiom} InstanceOfActionStore_bc(s_O: Joint.def.core.EntityStore, acts_O: Old.validation.typechecker.ActionStore, s_N: Joint.def.core.EntityStore, acts_N: New.validation.typechecker.ActionStore)
          decreases s_O, acts_O
          requires s_N == s_O
          requires acts_N == ActionStore_forward(acts_O)
          ensures New.validation.thm.base.InstanceOfActionStore(s_N, acts_N) == Old.validation.thm.base.InstanceOfActionStore(s_O, acts_O)

        lemma typeOfPrim_bc(p_O: Joint.def.core.Primitive, p_N: Joint.def.core.Primitive)
          decreases p_O
          requires p_N == p_O
          ensures New.validation.thm.base.typeOfPrim(p_N) == Type_forward(Old.validation.thm.base.typeOfPrim(p_O))
        {
          match p_O {
            case Bool(true) =>
              assert New.validation.thm.base.typeOfPrim(p_N) == Type_forward(Old.validation.types.Type.Bool(Old.validation.types.BoolType.True()));
            case Bool(false) =>
              assert New.validation.thm.base.typeOfPrim(p_N) == Type_forward(Old.validation.types.Type.Bool(Old.validation.types.BoolType.False()));
            case Int(_) =>
              assert New.validation.thm.base.typeOfPrim(p_N) == Type_forward(Old.validation.types.Type.Int());
            case String(_) =>
              assert New.validation.thm.base.typeOfPrim(p_N) == Type_forward(Old.validation.types.Type.String());
            case EntityUID(u) =>
              assert New.validation.thm.base.typeOfPrim(p_N) == Type_forward(Old.validation.types.Type.Entity(Old.validation.types.EntityLUB.EntityLUB({u.ty})));
          }
        }

        lemma {:axiom} InstanceOfBoolType_bc(b_O: bool, bt_O: Old.validation.types.BoolType, b_N: bool, bt_N: New.validation.types.BoolType)
          decreases b_O, bt_O
          requires b_N == b_O
          requires bt_N == BoolType_forward(bt_O)
          ensures New.validation.thm.base.InstanceOfBoolType(b_N, bt_N) == Old.validation.thm.base.InstanceOfBoolType(b_O, bt_O)

        lemma InstanceOfEntityLUB_bc(e_O: Joint.def.core.EntityUID, ty_O: Old.validation.types.EntityLUB, e_N: Joint.def.core.EntityUID, ty_N: New.validation.types.EntityLUB)
          decreases e_O, ty_O
          requires e_N == e_O
          requires ty_N == EntityLUB_forward(ty_O)
          ensures New.validation.thm.base.InstanceOfEntityLUB(e_N, ty_N) == Old.validation.thm.base.InstanceOfEntityLUB(e_O, ty_O)
        {
          match ty_O {
            case AnyEntity() =>
              assert New.validation.thm.base.InstanceOfEntityLUB(e_N, ty_N) == true;
            case EntityLUB(lub) =>
              if (exists et: Joint.def.core.EntityType ::
                et in lub && (InstanceOfEntityType_bc(e_O, et, e_N, et);
                Old.validation.thm.base.InstanceOfEntityType(e_O, et))) {
                var et :| et in lub && (InstanceOfEntityType_bc(e_O, et, e_N, et);
                Old.validation.thm.base.InstanceOfEntityType(e_O, et));
                assert New.validation.thm.base.InstanceOfEntityType(e_N, et) by {
                  InstanceOfEntityType_bc(e_O, et, e_N, et);
                }
              } else {
                forall et: Joint.def.core.EntityType | et in lub
                  ensures !New.validation.thm.base.InstanceOfEntityType(e_N, et) {
                  InstanceOfEntityType_bc(e_O, et, e_N, et);
                }
              }
          }
        }

        lemma InstanceOfType_bc(v_O: Joint.def.core.Value, ty_O: Old.validation.types.Type, v_N: Joint.def.core.Value, ty_N: New.validation.types.Type)
          decreases ty_O
          requires v_N == v_O
          requires ty_N == Type_forward(ty_O)
          ensures New.validation.thm.base.InstanceOfType(v_N, ty_N) == Old.validation.thm.base.InstanceOfType(v_O, ty_O)
        {
          match (v_O, ty_O) {
            case (Primitive(Bool(b)), Bool(bt)) =>
              InstanceOfBoolType_bc(b, bt, b, BoolType_forward(bt));
              assert New.validation.thm.base.InstanceOfType(v_N, ty_N) == Old.validation.thm.base.InstanceOfBoolType(b, bt);
            case (Primitive(Int(_)), Int()) =>
              assert New.validation.thm.base.InstanceOfType(v_N, ty_N) == true;
            case (Primitive(String(_)), String()) =>
              assert New.validation.thm.base.InstanceOfType(v_N, ty_N) == true;
            case (Primitive(EntityUID(e)), Entity(lub)) =>
              InstanceOfEntityLUB_bc(e, lub, e, EntityLUB_forward(lub));
              assert New.validation.thm.base.InstanceOfType(v_N, ty_N) == Old.validation.thm.base.InstanceOfEntityLUB(e, lub);
            case (Set(s), Set(ty1)) =>
              if (forall v1: Joint.def.core.Value :: v1 in s ==>
                (InstanceOfType_bc(v1, ty1, v1, Type_forward(ty1));
                Old.validation.thm.base.InstanceOfType(v1, ty1))) {
                forall v1: Joint.def.core.Value | v1 in s
                  ensures New.validation.thm.base.InstanceOfType(v1, Type_forward(ty1)) {
                  InstanceOfType_bc(v1, ty1, v1, Type_forward(ty1));
                }
              } else {
                var v1 :| v1 in s && !(InstanceOfType_bc(v1, ty1, v1, Type_forward(ty1));
                Old.validation.thm.base.InstanceOfType(v1, ty1));
                assert !New.validation.thm.base.InstanceOfType(v1, Type_forward(ty1)) by {
                  InstanceOfType_bc(v1, ty1, v1, Type_forward(ty1));
                }
              }
            case (Record(r), Record(rt)) =>
              assert New.validation.thm.base.InstanceOfType(v_N, ty_N) == ((!(RecordType_isOpen_bc(rt, RecordType_forward(rt));
              rt.isOpen()) ==> (forall k: string :: k in r ==> k in rt.attrs)) && (forall k: string :: k in rt.attrs && k in r ==>
                (InstanceOfType_bc(r[k], rt.attrs[k].ty, r[k], RecordType_forward(rt).attrs[k].ty);
                Old.validation.thm.base.InstanceOfType(r[k], rt.attrs[k].ty))) && (forall k: string :: k in rt.attrs && rt.attrs[k].isRequired ==> k in r));
            case (Extension(Decimal(_)), _) =>
              assert New.validation.thm.base.InstanceOfType(v_N, ty_N) == (ty_O == Old.validation.types.Type.Extension(Joint.def.base.Name.fromStr("decimal")));
            case (Extension(IPAddr(_)), _) =>
              assert New.validation.thm.base.InstanceOfType(v_N, ty_N) == (ty_O == Old.validation.types.Type.Extension(Joint.def.base.Name.fromStr("ipaddr")));
            case _ =>
              assert New.validation.thm.base.InstanceOfType(v_N, ty_N) == false;
          }
        }

        import opened def.base

        import opened def.core

        import opened def.engine

        import opened types

        import opened subtyping

        import opened typechecker
      }

      module model {
        import Joint

        import Old

        import New

        import Translations

        lemma IsTrue_bc(r_O: Joint.def.core.Request, s_O: Joint.def.core.EntityStore, e_O: Joint.def.core.Expr, r_N: Joint.def.core.Request, s_N: Joint.def.core.EntityStore, e_N: Joint.def.core.Expr)
          decreases r_O, s_O, e_O
          requires r_N == r_O
          requires s_N == s_O
          requires e_N == e_O
          ensures New.validation.thm.model.IsTrue(r_N, s_N, e_N) == Old.validation.thm.model.IsTrue(r_O, s_O, e_O)
        {
          IsSafe_bc(r_O, s_O, e_O, Old.validation.types.Type.Bool(Old.validation.types.BoolType.True()), r_N, s_N, e_N, New.validation.types.Type.Bool(New.validation.types.BoolType.True()));
          assert New.validation.thm.model.IsTrue(r_N, s_N, e_N) == Old.validation.thm.model.IsSafe(r_O, s_O, e_O, Old.validation.types.Type.Bool(Old.validation.types.BoolType.True()));
        }

        lemma IsFalse_bc(r_O: Joint.def.core.Request, s_O: Joint.def.core.EntityStore, e_O: Joint.def.core.Expr, r_N: Joint.def.core.Request, s_N: Joint.def.core.EntityStore, e_N: Joint.def.core.Expr)
          decreases r_O, s_O, e_O
          requires r_N == r_O
          requires s_N == s_O
          requires e_N == e_O
          ensures New.validation.thm.model.IsFalse(r_N, s_N, e_N) == Old.validation.thm.model.IsFalse(r_O, s_O, e_O)
        {
          IsSafe_bc(r_O, s_O, e_O, Old.validation.types.Type.Bool(Old.validation.types.BoolType.False()), r_N, s_N, e_N, New.validation.types.Type.Bool(New.validation.types.BoolType.False()));
          assert New.validation.thm.model.IsFalse(r_N, s_N, e_N) == Old.validation.thm.model.IsSafe(r_O, s_O, e_O, Old.validation.types.Type.Bool(Old.validation.types.BoolType.False()));
        }

        lemma GetAttrSafe_bc(r_O: Joint.def.core.Request, s_O: Joint.def.core.EntityStore, e_O: Joint.def.core.Expr, k_O: Joint.def.core.Attr, r_N: Joint.def.core.Request, s_N: Joint.def.core.EntityStore, e_N: Joint.def.core.Expr, k_N: Joint.def.core.Attr)
          decreases r_O, s_O, e_O, k_O
          requires r_N == r_O
          requires s_N == s_O
          requires e_N == e_O
          requires k_N == k_O
          ensures New.validation.thm.model.GetAttrSafe(r_N, s_N, e_N, k_N) == Old.validation.thm.model.GetAttrSafe(r_O, s_O, e_O, k_O)
        {
          IsTrue_bc(r_O, s_O, Joint.def.core.Expr.HasAttr(e_O, k_O), r_N, s_N, Joint.def.core.Expr.HasAttr(e_N, k_N));
          assert New.validation.thm.model.GetAttrSafe(r_N, s_N, e_N, k_N) == Old.validation.thm.model.IsTrue(r_O, s_O, Joint.def.core.Expr.HasAttr(e_O, k_O));
        }

        lemma IsTrueStrong_bc(r_O: Joint.def.core.Request, s_O: Joint.def.core.EntityStore, e_O: Joint.def.core.Expr, r_N: Joint.def.core.Request, s_N: Joint.def.core.EntityStore, e_N: Joint.def.core.Expr)
          decreases r_O, s_O, e_O
          requires r_N == r_O
          requires s_N == s_O
          requires e_N == e_O
          ensures New.validation.thm.model.IsTrueStrong(r_N, s_N, e_N) == Old.validation.thm.model.IsTrueStrong(r_O, s_O, e_O)
        {
          IsSafeStrong_bc(r_O, s_O, e_O, Old.validation.types.Type.Bool(Old.validation.types.BoolType.True()), r_N, s_N, e_N, New.validation.types.Type.Bool(New.validation.types.BoolType.True()));
          assert New.validation.thm.model.IsTrueStrong(r_N, s_N, e_N) == Old.validation.thm.model.IsSafeStrong(r_O, s_O, e_O, Old.validation.types.Type.Bool(Old.validation.types.BoolType.True()));
        }

        lemma IsFalseStrong_bc(r_O: Joint.def.core.Request, s_O: Joint.def.core.EntityStore, e_O: Joint.def.core.Expr, r_N: Joint.def.core.Request, s_N: Joint.def.core.EntityStore, e_N: Joint.def.core.Expr)
          decreases r_O, s_O, e_O
          requires r_N == r_O
          requires s_N == s_O
          requires e_N == e_O
          ensures New.validation.thm.model.IsFalseStrong(r_N, s_N, e_N) == Old.validation.thm.model.IsFalseStrong(r_O, s_O, e_O)
        {
          IsSafeStrong_bc(r_O, s_O, e_O, Old.validation.types.Type.Bool(Old.validation.types.BoolType.False()), r_N, s_N, e_N, New.validation.types.Type.Bool(New.validation.types.BoolType.False()));
          assert New.validation.thm.model.IsFalseStrong(r_N, s_N, e_N) == Old.validation.thm.model.IsSafeStrong(r_O, s_O, e_O, Old.validation.types.Type.Bool(Old.validation.types.BoolType.False()));
        }

        lemma SemanticSubty_bc(t1_O: Old.validation.types.Type, t2_O: Old.validation.types.Type, t1_N: New.validation.types.Type, t2_N: New.validation.types.Type)
          decreases t1_O, t2_O
          requires t1_N == Type_forward(t1_O)
          requires t2_N == Type_forward(t2_O)
          ensures New.validation.thm.model.SemanticSubty(t1_N, t2_N) == Old.validation.thm.model.SemanticSubty(t1_O, t2_O)
        {
          if (forall v: Joint.def.core.Value ::
            (InstanceOfType_bc(v, t1_O, v, t1_N);
            Old.validation.thm.base.InstanceOfType(v, t1_O)) ==>
            (InstanceOfType_bc(v, t2_O, v, t2_N);
            Old.validation.thm.base.InstanceOfType(v, t2_O))) {
            forall v: Joint.def.core.Value | InstanceOfType_bc(v, t1_O, v, t1_N);
            Old.validation.thm.base.InstanceOfType(v, t1_O)
              ensures New.validation.thm.base.InstanceOfType(v, t2_N) {
              InstanceOfType_bc(v, t2_O, v, t2_N);
            }
          } else {
            var v :| (InstanceOfType_bc(v, t1_O, v, t1_N);
            Old.validation.thm.base.InstanceOfType(v, t1_O)) && !(InstanceOfType_bc(v, t2_O, v, t2_N);
            Old.validation.thm.base.InstanceOfType(v, t2_O));
            assert !New.validation.thm.base.InstanceOfType(v, t2_N) by {
              InstanceOfType_bc(v, t2_O, v, t2_N);
            }
          }
        }

        lemma SemanticUB_bc(t1_O: Old.validation.types.Type, t2_O: Old.validation.types.Type, ub_O: Old.validation.types.Type, t1_N: New.validation.types.Type, t2_N: New.validation.types.Type, ub_N: New.validation.types.Type)
          decreases t1_O, t2_O, ub_O
          requires t1_N == Type_forward(t1_O)
          requires t2_N == Type_forward(t2_O)
          requires ub_N == Type_forward(ub_O)
          ensures New.validation.thm.model.SemanticUB(t1_N, t2_N, ub_N) == Old.validation.thm.model.SemanticUB(t1_O, t2_O, ub_O)
        {
          assert New.validation.thm.model.SemanticUB(t1_N, t2_N, ub_N) == ((SemanticSubty_bc(t1_O, ub_O, t1_N, ub_N);
          Old.validation.thm.model.SemanticSubty(t1_O, ub_O)) && (SemanticSubty_bc(t2_O, ub_O, t2_N, ub_N);
          Old.validation.thm.model.SemanticSubty(t2_O, ub_O)));
        }

        lemma ExistingEntityInLub_bc(s_O: Joint.def.core.EntityStore, ev_O: Joint.def.core.EntityUID, lub_O: Old.validation.types.EntityLUB, s_N: Joint.def.core.EntityStore, ev_N: Joint.def.core.EntityUID, lub_N: New.validation.types.EntityLUB)
          decreases s_O, ev_O, lub_O
          requires s_N == s_O
          requires ev_N == ev_O
          requires lub_N == EntityLUB_forward(lub_O)
          ensures New.validation.thm.model.ExistingEntityInLub(s_N, ev_N, lub_N) == Old.validation.thm.model.ExistingEntityInLub(s_O, ev_O, lub_O)
        {
          assert New.validation.thm.model.ExistingEntityInLub(s_N, ev_N, lub_N) == ((InstanceOfType_bc(Joint.def.core.Value.Primitive(Joint.def.core.Primitive.EntityUID(ev_O)), Old.validation.types.Type.Entity(lub_O), Joint.def.core.Value.Primitive(Joint.def.core.Primitive.EntityUID(ev_N)), New.validation.types.Type.Entity(lub_N));
          Old.validation.thm.base.InstanceOfType(Joint.def.core.Value.Primitive(Joint.def.core.Primitive.EntityUID(ev_O)), Old.validation.types.Type.Entity(lub_O))) && ev_O in s_O.entities);
        }

        lemma EntityProjStoreCondition_bc(s_O: Joint.def.core.EntityStore, l_O: Joint.def.core.Attr, lub_O: Old.validation.types.EntityLUB, t'_O: Old.validation.types.Type, isRequired_O: bool, s_N: Joint.def.core.EntityStore, l_N: Joint.def.core.Attr, lub_N: New.validation.types.EntityLUB, t'_N: New.validation.types.Type, isRequired_N: bool)
          decreases s_O, l_O, lub_O, t'_O, isRequired_O
          requires s_N == s_O
          requires l_N == l_O
          requires lub_N == EntityLUB_forward(lub_O)
          requires t'_N == Type_forward(t'_O)
          requires isRequired_N == isRequired_O
          ensures New.validation.thm.model.EntityProjStoreCondition(s_N, l_N, lub_N, t'_N, isRequired_N) == Old.validation.thm.model.EntityProjStoreCondition(s_O, l_O, lub_O, t'_O, isRequired_O)
        {
          if (forall ev: Joint.def.core.EntityUID ::
            (ExistingEntityInLub_bc(s_O, ev, lub_O, s_N, ev, lub_N);
            Old.validation.thm.model.ExistingEntityInLub(s_O, ev, lub_O)) ==>
            (isRequired_O ==> l_O in s_O.entities[ev].attrs) && (l_O in s_O.entities[ev].attrs ==> (InstanceOfType_bc(s_O.entities[ev].attrs[l_O], t'_O, s_N.entities[ev].attrs[l_N], t'_N);
            Old.validation.thm.base.InstanceOfType(s_O.entities[ev].attrs[l_O], t'_O)))) {
            forall ev: Joint.def.core.EntityUID | ExistingEntityInLub_bc(s_O, ev, lub_O, s_N, ev, lub_N);
            Old.validation.thm.model.ExistingEntityInLub(s_O, ev, lub_O)
              ensures (isRequired_N ==> l_N in s_N.entities[ev].attrs) && (l_N in s_N.entities[ev].attrs ==> New.validation.thm.base.InstanceOfType(s_N.entities[ev].attrs[l_N], t'_N)) {
              InstanceOfType_bc(s_O.entities[ev].attrs[l_O], t'_O, s_N.entities[ev].attrs[l_N], t'_N);
            }
          } else {
            var ev :| (ExistingEntityInLub_bc(s_O, ev, lub_O, s_N, ev, lub_N);
            Old.validation.thm.model.ExistingEntityInLub(s_O, ev, lub_O)) && !((isRequired_O ==> l_O in s_O.entities[ev].attrs) && (l_O in s_O.entities[ev].attrs ==> (InstanceOfType_bc(s_O.entities[ev].attrs[l_O], t'_O, s_N.entities[ev].attrs[l_N], t'_N);
            Old.validation.thm.base.InstanceOfType(s_O.entities[ev].attrs[l_O], t'_O))));
            assert !((isRequired_N ==> l_N in s_N.entities[ev].attrs) && (l_N in s_N.entities[ev].attrs ==> New.validation.thm.base.InstanceOfType(s_N.entities[ev].attrs[l_N], t'_N))) by {
              InstanceOfType_bc(s_O.entities[ev].attrs[l_O], t'_O, s_N.entities[ev].attrs[l_N], t'_N);
            }
          }
        }

        lemma {:axiom} EntityInEntity_bc(s_O: Joint.def.core.EntityStore, u1_O: Joint.def.core.EntityUID, u2_O: Joint.def.core.EntityUID, s_N: Joint.def.core.EntityStore, u1_N: Joint.def.core.EntityUID, u2_N: Joint.def.core.EntityUID)
          decreases s_O, u1_O, u2_O
          requires s_N == s_O
          requires u1_N == u1_O
          requires u2_N == u2_O
          ensures New.validation.thm.model.EntityInEntity(s_N, u1_N, u2_N) == Old.validation.thm.model.EntityInEntity(s_O, u1_O, u2_O)

        lemma IsSafe_bc(r_O: Joint.def.core.Request, s_O: Joint.def.core.EntityStore, e_O: Joint.def.core.Expr, t_O: Old.validation.types.Type, r_N: Joint.def.core.Request, s_N: Joint.def.core.EntityStore, e_N: Joint.def.core.Expr, t_N: New.validation.types.Type)
          decreases r_O, s_O, e_O, t_O
          requires r_N == r_O
          requires s_N == s_O
          requires e_N == e_O
          requires t_N == Type_forward(t_O)
          ensures New.validation.thm.model.IsSafe(r_N, s_N, e_N, t_N) == Old.validation.thm.model.IsSafe(r_O, s_O, e_O, t_O)
        {
          reveal Old.validation.thm.model.IsSafe();
          reveal New.validation.thm.model.IsSafe();
          assert New.validation.thm.model.IsSafe(r_N, s_N, e_N, t_N) == ((Evaluate_bc(e_O, r_O, s_O, e_N, r_N, s_N);
          Old.validation.thm.base.Evaluate(e_O, r_O, s_O)) == Joint.def.base.Err(Joint.def.base.Error.EntityDoesNotExist()) || (Evaluate_bc(e_O, r_O, s_O, e_N, r_N, s_N);
          Old.validation.thm.base.Evaluate(e_O, r_O, s_O)) == Joint.def.base.Err(Joint.def.base.Error.ExtensionError()) || ((Evaluate_bc(e_O, r_O, s_O, e_N, r_N, s_N);
          Old.validation.thm.base.Evaluate(e_O, r_O, s_O)).Ok? && (InstanceOfType_bc(Old.validation.thm.base.Evaluate(e_O, r_O, s_O).value, t_O, New.validation.thm.base.Evaluate(e_N, r_N, s_N).value, t_N);
          Old.validation.thm.base.InstanceOfType((Evaluate_bc(e_O, r_O, s_O, e_N, r_N, s_N);
          Old.validation.thm.base.Evaluate(e_O, r_O, s_O)).value, t_O))));
        }

        lemma IsSafeStrong_bc(r_O: Joint.def.core.Request, s_O: Joint.def.core.EntityStore, e_O: Joint.def.core.Expr, t_O: Old.validation.types.Type, r_N: Joint.def.core.Request, s_N: Joint.def.core.EntityStore, e_N: Joint.def.core.Expr, t_N: New.validation.types.Type)
          decreases r_O, s_O, e_O, t_O
          requires r_N == r_O
          requires s_N == s_O
          requires e_N == e_O
          requires t_N == Type_forward(t_O)
          ensures New.validation.thm.model.IsSafeStrong(r_N, s_N, e_N, t_N) == Old.validation.thm.model.IsSafeStrong(r_O, s_O, e_O, t_O)
        {
          reveal Old.validation.thm.model.IsSafeStrong();
          reveal New.validation.thm.model.IsSafeStrong();
          assert New.validation.thm.model.IsSafeStrong(r_N, s_N, e_N, t_N) == ((IsSafe_bc(r_O, s_O, e_O, t_O, r_N, s_N, e_N, t_N);
          Old.validation.thm.model.IsSafe(r_O, s_O, e_O, t_O)) && (Evaluate_bc(e_O, r_O, s_O, e_N, r_N, s_N);
          Old.validation.thm.base.Evaluate(e_O, r_O, s_O)).Ok?);
        }

        lemma ExtensionFunSafeRequires_bc(name_O: Joint.def.base.Name, args_O: seq<Joint.def.core.Value>, name_N: Joint.def.base.Name, args_N: seq<Joint.def.core.Value>)
          decreases name_O, args_O
          requires name_O in Old.validation.ext.extFunTypes
          requires name_N == name_O
          requires args_N == args_O
          ensures name_N in New.validation.ext.extFunTypes
          ensures New.validation.thm.model.ExtensionFunSafeRequires(name_N, args_N) == Old.validation.thm.model.ExtensionFunSafeRequires(name_O, args_O)
        {
          var eft := Old.validation.ext.extFunTypes[name_O];
          assert New.validation.thm.model.ExtensionFunSafeRequires(name_N, args_N) == (|args_O| == |eft.args| && (forall i: int :: 0 <= i && i < |args_O| ==>
            (InstanceOfType_bc(args_O[i], eft.args[i], args_N[i], ExtFunType_forward(eft).args[i]);
            Old.validation.thm.base.InstanceOfType(args_O[i], eft.args[i]))));
        }

        lemma ExtensionFunSafeEnsures_bc(name_O: Joint.def.base.Name, args_O: seq<Joint.def.core.Value>, name_N: Joint.def.base.Name, args_N: seq<Joint.def.core.Value>)
          decreases name_O, args_O
          requires name_O in Old.validation.ext.extFunTypes
          requires name_N == name_O
          requires args_N == args_O
          ensures name_N in New.validation.ext.extFunTypes
          ensures New.validation.thm.model.ExtensionFunSafeEnsures(name_N, args_N) == Old.validation.thm.model.ExtensionFunSafeEnsures(name_O, args_O)
        {
          var eft := Old.validation.ext.extFunTypes[name_O];
          var res := Joint.def.core.extFuns[name_O].fun(args_O);
          assert New.validation.thm.model.ExtensionFunSafeEnsures(name_N, args_N) == (res == Joint.def.base.Err(Joint.def.base.Error.ExtensionError()) || (res.Ok? && (InstanceOfType_bc(res.value, eft.ret, res.value, ExtFunType_forward(eft).ret);
          Old.validation.thm.base.InstanceOfType(res.value, eft.ret))));
        }

        lemma {:axiom} IsDecimalConstructorName_bc(name_O: Joint.def.base.Name, name_N: Joint.def.base.Name)
          decreases name_O
          requires name_N == name_O
          ensures New.validation.thm.model.IsDecimalConstructorName(name_N) == Old.validation.thm.model.IsDecimalConstructorName(name_O)

        lemma {:axiom} IsDecimalComparisonName_bc(name_O: Joint.def.base.Name, name_N: Joint.def.base.Name)
          decreases name_O
          requires name_N == name_O
          ensures New.validation.thm.model.IsDecimalComparisonName(name_N) == Old.validation.thm.model.IsDecimalComparisonName(name_O)

        lemma {:axiom} IsIpConstructorName_bc(name_O: Joint.def.base.Name, name_N: Joint.def.base.Name)
          decreases name_O
          requires name_N == name_O
          ensures New.validation.thm.model.IsIpConstructorName(name_N) == Old.validation.thm.model.IsIpConstructorName(name_O)

        lemma {:axiom} IsIpUnaryName_bc(name_O: Joint.def.base.Name, name_N: Joint.def.base.Name)
          decreases name_O
          requires name_N == name_O
          ensures New.validation.thm.model.IsIpUnaryName(name_N) == Old.validation.thm.model.IsIpUnaryName(name_O)

        lemma {:axiom} IsIpBinaryName_bc(name_O: Joint.def.base.Name, name_N: Joint.def.base.Name)
          decreases name_O
          requires name_N == name_O
          ensures New.validation.thm.model.IsIpBinaryName(name_N) == Old.validation.thm.model.IsIpBinaryName(name_O)

        lemma ExistsSafeType_bc(r_O: Joint.def.core.Request, s_O: Joint.def.core.EntityStore, e_O: Joint.def.core.Expr, r_N: Joint.def.core.Request, s_N: Joint.def.core.EntityStore, e_N: Joint.def.core.Expr)
          decreases r_O, s_O, e_O
          requires r_N == r_O
          requires s_N == s_O
          requires e_N == e_O
          ensures New.validation.thm.model.ExistsSafeType(r_N, s_N, e_N) == Old.validation.thm.model.ExistsSafeType(r_O, s_O, e_O)
        {
          if (exists t: Old.validation.types.Type ::
            (IsSafe_bc(r_O, s_O, e_O, t, r_N, s_N, e_N, Type_forward(t));
            Old.validation.thm.model.IsSafe(r_O, s_O, e_O, t))) {
            var t :| (IsSafe_bc(r_O, s_O, e_O, t, r_N, s_N, e_N, Type_forward(t));
            Old.validation.thm.model.IsSafe(r_O, s_O, e_O, t));
            assert New.validation.thm.model.IsSafe(r_N, s_N, e_N, Type_forward(t)) by {
              IsSafe_bc(r_O, s_O, e_O, t, r_N, s_N, e_N, Type_forward(t));
            }
          } else {
            forall t: Old.validation.types.Type
              ensures !New.validation.thm.model.IsSafe(r_N, s_N, e_N, Type_forward(t)) {
              IsSafe_bc(r_O, s_O, e_O, t, r_N, s_N, e_N, Type_forward(t));
            }
          }
        }

        import opened def

        import opened def.core

        import opened def.engine

        import opened def.util

        import opened eval.basic

        import opened types

        import opened subtyping

        import opened base

        import opened ext
      }

      module toplevel {
        import Joint

        import Old

        import New

        import Translations

        lemma SatisfiesSchema_bc(request_O: Joint.def.core.Request, entities_O: Joint.def.core.EntityStore, schema_O: Old.validation.thm.toplevel.Schema, request_N: Joint.def.core.Request, entities_N: Joint.def.core.EntityStore, schema_N: New.validation.thm.toplevel.Schema)
          decreases request_O, entities_O, schema_O
          requires request_N == request_O
          requires entities_N == entities_O
          requires schema_N == Schema_forward(schema_O)
          ensures New.validation.thm.toplevel.SatisfiesSchema(request_N, entities_N, schema_N) == Old.validation.thm.toplevel.SatisfiesSchema(request_O, entities_O, schema_O)
        {
          assert New.validation.thm.toplevel.SatisfiesSchema(request_N, entities_N, schema_N) == ((InstanceOfRequestType_bc(request_O, schema_O.reqty, request_N, schema_N.reqty);
          Old.validation.thm.base.InstanceOfRequestType(request_O, schema_O.reqty)) && (InstanceOfEntityTypeStore_bc(entities_O, schema_O.ets, entities_N, schema_N.ets);
          Old.validation.thm.base.InstanceOfEntityTypeStore(entities_O, schema_O.ets)) && (InstanceOfActionStore_bc(entities_O, schema_O.acts, entities_N, schema_N.acts);
          Old.validation.thm.base.InstanceOfActionStore(entities_O, schema_O.acts)));
        }

        lemma permissiveTypecheck_bc(pid_O: Joint.def.core.PolicyID, policies_O: Joint.def.core.PolicyStore, schema_O: Old.validation.thm.toplevel.Schema, pid_N: Joint.def.core.PolicyID, policies_N: Joint.def.core.PolicyStore, schema_N: New.validation.thm.toplevel.Schema)
          decreases pid_O, policies_O, schema_O
          requires pid_O in policies_O.policies.Keys
          requires pid_N == pid_O
          requires policies_N == policies_O
          requires schema_N == Schema_forward(schema_O)
          ensures pid_N in policies_N.policies.Keys
          ensures New.validation.thm.toplevel.permissiveTypecheck(pid_N, policies_N, schema_N) == types.Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.thm.toplevel.permissiveTypecheck(pid_O, policies_O, schema_O))
        {
          var typechecker := Old.validation.typechecker.Typechecker.Typechecker(schema_O.ets, schema_O.acts, schema_O.reqty);
          {
            Typechecker_typecheck_bc(typechecker, Typechecker_forward(typechecker), policies_O.policies[pid_O].toExpr(), Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool()), policies_N.policies[pid_N].toExpr(), New.validation.types.Type.Bool(New.validation.types.BoolType.AnyBool()));
            assert New.validation.thm.toplevel.permissiveTypecheck(pid_N, policies_N, schema_N) == types.Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), typechecker.typecheck(policies_O.policies[pid_O].toExpr(), Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool())));
          }
        }

        lemma strictTypecheck_bc(pid_O: Joint.def.core.PolicyID, policies_O: Joint.def.core.PolicyStore, schema_O: Old.validation.thm.toplevel.Schema, pid_N: Joint.def.core.PolicyID, policies_N: Joint.def.core.PolicyStore, schema_N: New.validation.thm.toplevel.Schema)
          decreases pid_O, policies_O, schema_O
          requires pid_O in policies_O.policies.Keys
          requires pid_N == pid_O
          requires policies_N == policies_O
          requires schema_N == Schema_forward(schema_O)
          ensures pid_N in policies_N.policies.Keys
          ensures New.validation.thm.toplevel.strictTypecheck(pid_N, policies_N, schema_N) == strict.Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.validation.thm.toplevel.strictTypecheck(pid_O, policies_O, schema_O))
        {
          var typechecker := Old.validation.strict.StrictTypechecker.StrictTypechecker(schema_O.ets, schema_O.acts, schema_O.reqty); assert New.validation.thm.toplevel.strictTypecheck(pid_N, policies_N, schema_N) == strict.Result_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), typechecker.typecheck(policies_O.policies[pid_O].toExpr(), Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool())));
        }

        import strict

        import opened typechecker

        import opened types

        import opened base

        import opened model

        import opened soundness

        import opened def.core

        import opened def.engine

        function Schema_forward(S_O: Old.validation.thm.toplevel.Schema): New.validation.thm.toplevel.Schema
        {
          match S_O {
            case Schema(reqty_O, ets_O, acts_O) =>
              /* unchanged constructor */ New.validation.thm.toplevel.Schema.Schema(RequestType_forward(reqty_O), EntityTypeStore_forward(ets_O), ActionStore_forward(acts_O))
          }
        }

        function Schema_backward(S_N: New.validation.thm.toplevel.Schema): Old.validation.thm.toplevel.Schema
        {
          match S_N {
            case Schema(reqty_N, ets_N, acts_N) =>
              /* unchanged constructor */ Old.validation.thm.toplevel.Schema.Schema(RequestType_backward(reqty_N), EntityTypeStore_backward(ets_N), ActionStore_backward(acts_N))
          }
        }
      }

      module soundness {
        import Joint

        import Old

        import New

        import Translations

        import opened def

        import opened def.core

        import opened def.engine

        import opened def.util

        import opened eval.basic

        import opened types

        import opened subtyping

        import opened typechecker

        import opened model

        import opened base

        import opened ext

        function Result_forward<T_O, T_N>(T_forward: T_O->T_N, T_backward: T_N->T_O, R_O: Old.validation.thm.soundness.Result<T_O>): New.validation.thm.soundness.Result<T_N>
        {
          types.Result_forward(T_forward, T_backward, R_O)
        }

        function Result_backward<T_O, T_N>(T_forward: T_O->T_N, T_backward: T_N->T_O, R_N: New.validation.thm.soundness.Result<T_N>): Old.validation.thm.soundness.Result<T_O>
        {
          types.Result_backward(T_forward, T_backward, R_N)
        }

        function SemanticSoundnessProof_forward(S_O: Old.validation.thm.soundness.SemanticSoundnessProof): New.validation.thm.soundness.SemanticSoundnessProof
        {
          match S_O {
            case SSP(reqty_O, ets_O, acts_O, r_O, s_O) =>
              /* unchanged constructor */ New.validation.thm.soundness.SemanticSoundnessProof.SSP(RequestType_forward(reqty_O), EntityTypeStore_forward(ets_O), ActionStore_forward(acts_O), r_O, s_O)
          }
        }

        function SemanticSoundnessProof_backward(S_N: New.validation.thm.soundness.SemanticSoundnessProof): Old.validation.thm.soundness.SemanticSoundnessProof
        {
          match S_N {
            case SSP(reqty_N, ets_N, acts_N, r_N, s_N) =>
              /* unchanged constructor */ Old.validation.thm.soundness.SemanticSoundnessProof.SSP(RequestType_backward(reqty_N), EntityTypeStore_backward(ets_N), ActionStore_backward(acts_N), r_N, s_N)
          }
        }

        lemma SemanticSoundnessProof_WellTyped_bc(S_O: Old.validation.thm.soundness.SemanticSoundnessProof, S_N: New.validation.thm.soundness.SemanticSoundnessProof, e_O: Joint.def.core.Expr, effs_O: Old.validation.typechecker.Effects, e_N: Joint.def.core.Expr, effs_N: New.validation.typechecker.Effects)
          decreases S_O, e_O, effs_O
          requires S_N == SemanticSoundnessProof_forward(S_O)
          requires e_N == e_O
          requires effs_N == Effects_forward(effs_O)
          ensures S_N.WellTyped(e_N, effs_N) == S_O.WellTyped(e_O, effs_O)
        {
          assert S_N.WellTyped(e_N, effs_N) == (Typechecker_infer_bc(S_O.TC, S_N.TC, e_O, effs_O, e_N, effs_N);
          S_O.TC.infer(e_O, effs_O)).Ok?;
        }

        lemma SemanticSoundnessProof_getType_bc(S_O: Old.validation.thm.soundness.SemanticSoundnessProof, S_N: New.validation.thm.soundness.SemanticSoundnessProof, e_O: Joint.def.core.Expr, effs_O: Old.validation.typechecker.Effects, e_N: Joint.def.core.Expr, effs_N: New.validation.typechecker.Effects)
          decreases S_O, e_O, effs_O
          requires S_O.WellTyped(e_O, effs_O)
          requires S_N == SemanticSoundnessProof_forward(S_O)
          requires e_N == e_O
          requires effs_N == Effects_forward(effs_O)
          ensures S_N.WellTyped(e_N, effs_N)
          ensures S_N.getType(e_N, effs_N) == Type_forward(S_O.getType(e_O, effs_O))
        {
          assert S_N.getType(e_N, effs_N) == Type_forward((Typechecker_infer_bc(S_O.TC, S_N.TC, e_O, effs_O, e_N, effs_N);
          S_O.TC.infer(e_O, effs_O)).value.0);
        }

        lemma SemanticSoundnessProof_getEffects_bc(S_O: Old.validation.thm.soundness.SemanticSoundnessProof, S_N: New.validation.thm.soundness.SemanticSoundnessProof, e_O: Joint.def.core.Expr, effs_O: Old.validation.typechecker.Effects, e_N: Joint.def.core.Expr, effs_N: New.validation.typechecker.Effects)
          decreases S_O, e_O, effs_O
          requires S_O.WellTyped(e_O, effs_O)
          requires S_N == SemanticSoundnessProof_forward(S_O)
          requires e_N == e_O
          requires effs_N == Effects_forward(effs_O)
          ensures S_N.WellTyped(e_N, effs_N)
          ensures S_N.getEffects(e_N, effs_N) == Effects_forward(S_O.getEffects(e_O, effs_O))
        {
          assert S_N.getEffects(e_N, effs_N) == Effects_forward((Typechecker_infer_bc(S_O.TC, S_N.TC, e_O, effs_O, e_N, effs_N);
          S_O.TC.infer(e_O, effs_O)).value.1);
        }

        lemma SemanticSoundnessProof_Typesafe_bc(S_O: Old.validation.thm.soundness.SemanticSoundnessProof, S_N: New.validation.thm.soundness.SemanticSoundnessProof, e_O: Joint.def.core.Expr, effs_O: Old.validation.typechecker.Effects, t_O: Old.validation.types.Type, e_N: Joint.def.core.Expr, effs_N: New.validation.typechecker.Effects, t_N: New.validation.types.Type)
          decreases S_O, e_O, effs_O, t_O
          requires S_N == SemanticSoundnessProof_forward(S_O)
          requires e_N == e_O
          requires effs_N == Effects_forward(effs_O)
          requires t_N == Type_forward(t_O)
          ensures S_N.Typesafe(e_N, effs_N, t_N) == S_O.Typesafe(e_O, effs_O, t_O)
        {
          assert S_N.Typesafe(e_N, effs_N, t_N) == ((SemanticSoundnessProof_WellTyped_bc(S_O, S_N, e_O, effs_O, e_N, effs_N);
          S_O.WellTyped(e_O, effs_O)) && Old.validation.subtyping.subty(SemanticSoundnessProof_getType_bc(S_O, S_N, e_O, effs_O, e_N, effs_N);
          S_O.getType(e_O, effs_O), t_O));
        }

        lemma SemanticSoundnessProof_WellFormedRequestAndStore_bc(S_O: Old.validation.thm.soundness.SemanticSoundnessProof, S_N: New.validation.thm.soundness.SemanticSoundnessProof)
          decreases S_O
          requires S_N == SemanticSoundnessProof_forward(S_O)
          ensures S_N.WellFormedRequestAndStore() == S_O.WellFormedRequestAndStore()
        {
          reveal S_O.WellFormedRequestAndStore();
          reveal S_N.WellFormedRequestAndStore();
          assert S_N.WellFormedRequestAndStore() == ((InstanceOfRequestType_bc(S_O.r, S_O.reqty, S_N.r, S_N.reqty);
          Old.validation.thm.base.InstanceOfRequestType(S_O.r, S_O.reqty)) && (InstanceOfEntityTypeStore_bc(S_O.s, S_O.ets, S_N.s, S_N.ets);
          Old.validation.thm.base.InstanceOfEntityTypeStore(S_O.s, S_O.ets)) && (InstanceOfActionStore_bc(S_O.s, S_O.acts, S_N.s, S_N.acts);
          Old.validation.thm.base.InstanceOfActionStore(S_O.s, S_O.acts)));
        }

        lemma SemanticSoundnessProof_EffectsInvariant_bc(S_O: Old.validation.thm.soundness.SemanticSoundnessProof, S_N: New.validation.thm.soundness.SemanticSoundnessProof, effs_O: Old.validation.typechecker.Effects, effs_N: New.validation.typechecker.Effects)
          decreases S_O, effs_O
          requires S_N == SemanticSoundnessProof_forward(S_O)
          requires effs_N == Effects_forward(effs_O)
          ensures S_N.EffectsInvariant(effs_N) == S_O.EffectsInvariant(effs_O)
        {
          reveal S_O.EffectsInvariant();
          reveal S_N.EffectsInvariant();
          if (forall e: Joint.def.core.Expr, k: Joint.def.core.Attr :: (e, k) in effs_O.effs ==>
            (GetAttrSafe_bc(S_O.r, S_O.s, e, k, S_N.r, S_N.s, e, k);
            Old.validation.thm.model.GetAttrSafe(S_O.r, S_O.s, e, k))) {
            forall e: Joint.def.core.Expr, k: Joint.def.core.Attr | (e, k) in effs_O.effs
              ensures New.validation.thm.model.GetAttrSafe(S_N.r, S_N.s, e, k) {
              GetAttrSafe_bc(S_O.r, S_O.s, e, k, S_N.r, S_N.s, e, k);
            }
          } else {
            var e, k :| (e, k) in effs_O.effs && !(GetAttrSafe_bc(S_O.r, S_O.s, e, k, S_N.r, S_N.s, e, k);
            Old.validation.thm.model.GetAttrSafe(S_O.r, S_O.s, e, k));
            assert !New.validation.thm.model.GetAttrSafe(S_N.r, S_N.s, e, k) by {
              GetAttrSafe_bc(S_O.r, S_O.s, e, k, S_N.r, S_N.s, e, k);
            }
          }
        }

        lemma SemanticSoundnessProof_GuardedEffectsInvariant_bc(S_O: Old.validation.thm.soundness.SemanticSoundnessProof, S_N: New.validation.thm.soundness.SemanticSoundnessProof, e_O: Joint.def.core.Expr, effs_O: Old.validation.typechecker.Effects, e_N: Joint.def.core.Expr, effs_N: New.validation.typechecker.Effects)
          decreases S_O, e_O, effs_O
          requires S_N == SemanticSoundnessProof_forward(S_O)
          requires e_N == e_O
          requires effs_N == Effects_forward(effs_O)
          ensures S_N.GuardedEffectsInvariant(e_N, effs_N) == S_O.GuardedEffectsInvariant(e_O, effs_O)
        {
          assert S_N.GuardedEffectsInvariant(e_N, effs_N) == ((IsTrueStrong_bc(S_O.r, S_O.s, e_O, S_N.r, S_N.s, e_N);
          Old.validation.thm.model.IsTrueStrong(S_O.r, S_O.s, e_O)) ==> (SemanticSoundnessProof_EffectsInvariant_bc(S_O, S_N, effs_O, effs_N);
          S_O.EffectsInvariant(effs_O)));
        }
      }
    }
  }

  module eval {
    import Joint

    import Old

    import New

    import Translations

    module basic {
      import Joint

      import Old

      import New

      import Translations

      import opened def.base

      import opened def.core

      import opened def.engine

      import opened def.util
    }
  }

  module difftest {
    import Joint

    import Old

    import New

    import Translations

    module helpers {
      import Joint

      import Old

      import New

      import Translations

      lemma {:axiom} mapSeq_bc<A_O, A_N, B_O, B_N>(A_forward: A_O->A_N, A_backward: A_N->A_O, B_forward: B_O->B_N, B_backward: B_N->B_O, f_O: A_O->B_O, s_O: seq<A_O>, f_N: A_N->B_N, s_N: seq<A_N>)
        decreases s_O
        requires forall i: int :: 0 <= i && i < |s_O| ==> f_O.requires(s_O[i])
        requires forall x1_O: A_O :: f_N(A_forward(x1_O)) == B_forward(f_O(x1_O))
        requires s_N == Translations.MapBuiltinTypes.Seq(A_forward, s_O)
        requires forall x_O: A_O :: A_backward(A_forward(x_O)) == x_O
        requires forall x_O: B_O :: B_backward(B_forward(x_O)) == x_O
        ensures forall i: int :: 0 <= i && i < |s_N| ==> f_N.requires(s_N[i])
        ensures New.difftest.helpers.mapSeq(f_N, s_N) == Translations.MapBuiltinTypes.Seq(B_forward, Old.difftest.helpers.mapSeq(f_O, s_O))

      lemma {:axiom} getJsonBool_bc(j_O: Old.difftest.helpers.Json, j_N: New.difftest.helpers.Json)
        decreases j_O
        requires j_N == Json_forward(j_O)
        ensures New.difftest.helpers.getJsonBool(j_N) == FromProdResult_forward((x: bool) => x, (x: bool) => x, Old.difftest.helpers.getJsonBool(j_O))

      lemma {:axiom} getJsonField_bc(j_O: Old.difftest.helpers.Json, f_O: string, j_N: New.difftest.helpers.Json, f_N: string)
        decreases j_O, f_O
        requires j_N == Json_forward(j_O)
        requires f_N == f_O
        ensures New.difftest.helpers.getJsonField(j_N, f_N) == FromProdResult_forward((x: Old.difftest.helpers.Json) => Json_forward(x), (x: New.difftest.helpers.Json) => Json_backward(x), Old.difftest.helpers.getJsonField(j_O, f_O))

      lemma {:axiom} unpackJsonSum_bc(j_O: Old.difftest.helpers.Json, j_N: New.difftest.helpers.Json)
        decreases j_O
        requires j_N == Json_forward(j_O)
        ensures New.difftest.helpers.unpackJsonSum(j_N) == FromProdResult_forward((x: (string,Old.difftest.helpers.Json)) => (x.0, Json_forward(x.1)), (x: (string,New.difftest.helpers.Json)) => (x.0, Json_backward(x.1)), Old.difftest.helpers.unpackJsonSum(j_O))

      lemma {:axiom} mapFromEntriesProd_bc<K_O, K_N, V_O, V_N>(K_forward: K_O->K_N, K_backward: K_N->K_O, V_forward: V_O->V_N, V_backward: V_N->V_O, entries_O: seq<(K_O,V_O)>, entries_N: seq<(K_N,V_N)>)
        decreases entries_O
        requires entries_N == Translations.MapBuiltinTypes.Seq((sq: (K_O,V_O)) => (K_forward(sq.0), V_forward(sq.1)), entries_O)
        requires forall x_O: K_O :: K_backward(K_forward(x_O)) == x_O
        requires forall x_O: V_O :: V_backward(V_forward(x_O)) == x_O
        ensures New.difftest.helpers.mapFromEntriesProd(entries_N) == FromProdResult_forward((x: map<K_O,V_O>) => Translations.MapBuiltinTypes.Map(K_forward, K_backward, V_forward, x), (x: map<K_N,V_N>) => Translations.MapBuiltinTypes.Map(K_backward, K_forward, V_backward, x), Old.difftest.helpers.mapFromEntriesProd(entries_O))

      lemma {:axiom} deserializeField_bc<F_O, F_N>(F_forward: F_O->F_N, F_backward: F_N->F_O, j_O: Old.difftest.helpers.Json, fn_O: string, fd_O: Old.difftest.helpers.PartialDeserializer<F_O>, j_N: New.difftest.helpers.Json, fn_N: string, fd_N: New.difftest.helpers.PartialDeserializer<F_N>)
        decreases j_O, fn_O
        requires Old.difftest.helpers.deserializerAcceptsSubterms(fd_O, j_O)
        requires j_N == Json_forward(j_O)
        requires fn_N == fn_O
        requires fd_N == PartialDeserializer_forward(F_forward, F_backward, fd_O)
        requires forall x_O: F_O :: F_backward(F_forward(x_O)) == x_O
        ensures New.difftest.helpers.deserializerAcceptsSubterms(fd_N, j_N)
        ensures New.difftest.helpers.deserializeField(j_N, fn_N, fd_N) == FromProdResult_forward(F_forward, F_backward, Old.difftest.helpers.deserializeField(j_O, fn_O, fd_O))

      lemma {:axiom} objDeserializer3Fields_bc<T_O, T_N, F1_O, F1_N, F2_O, F2_N, F3_O, F3_N>(T_forward: T_O->T_N, T_backward: T_N->T_O, F1_forward: F1_O->F1_N, F1_backward: F1_N->F1_O, F2_forward: F2_O->F2_N, F2_backward: F2_N->F2_O, F3_forward: F3_O->F3_N, F3_backward: F3_N->F3_O, fn1_O: string, fd1_O: Old.difftest.helpers.Deserializer<F1_O>, fn2_O: string, fd2_O: Old.difftest.helpers.Deserializer<F2_O>, fn3_O: string, fd3_O: Old.difftest.helpers.Deserializer<F3_O>, cons_O: (F1_O,F2_O,F3_O)->Old.difftest.helpers.FromProdResult<T_O>, fn1_N: string, fd1_N: New.difftest.helpers.Deserializer<F1_N>, fn2_N: string, fd2_N: New.difftest.helpers.Deserializer<F2_N>, fn3_N: string, fd3_N: New.difftest.helpers.Deserializer<F3_N>, cons_N: (F1_N,F2_N,F3_N)->New.difftest.helpers.FromProdResult<T_N>)
        decreases fn1_O, fn2_O, fn3_O
        requires fn1_N == fn1_O
        requires fd1_N == Deserializer_forward(F1_forward, F1_backward, fd1_O)
        requires fn2_N == fn2_O
        requires fd2_N == Deserializer_forward(F2_forward, F2_backward, fd2_O)
        requires fn3_N == fn3_O
        requires fd3_N == Deserializer_forward(F3_forward, F3_backward, fd3_O)
        requires forall x1_O: F1_O, x2_O: F2_O, x3_O: F3_O :: cons_N(F1_forward(x1_O), F2_forward(x2_O), F3_forward(x3_O)) == FromProdResult_forward(T_forward, T_backward, cons_O(x1_O, x2_O, x3_O))
        requires forall x_O: T_O :: T_backward(T_forward(x_O)) == x_O
        requires forall x_O: F1_O :: F1_backward(F1_forward(x_O)) == x_O
        requires forall x_O: F2_O :: F2_backward(F2_forward(x_O)) == x_O
        requires forall x_O: F3_O :: F3_backward(F3_forward(x_O)) == x_O
        ensures New.difftest.helpers.objDeserializer3Fields(fn1_N, fd1_N, fn2_N, fd2_N, fn3_N, fd3_N, cons_N) == Deserializer_forward(T_forward, T_backward, Old.difftest.helpers.objDeserializer3Fields(fn1_O, fd1_O, fn2_O, fd2_O, fn3_O, fd3_O, cons_O))

      lemma {:axiom} deserializeTuple2Elts_bc<T_O, T_N, E1_O, E1_N, E2_O, E2_N>(T_forward: T_O->T_N, T_backward: T_N->T_O, E1_forward: E1_O->E1_N, E1_backward: E1_N->E1_O, E2_forward: E2_O->E2_N, E2_backward: E2_N->E2_O, j_O: Old.difftest.helpers.Json, ed1_O: Old.difftest.helpers.PartialDeserializer<E1_O>, ed2_O: Old.difftest.helpers.PartialDeserializer<E2_O>, cons_O: (E1_O,E2_O)->Old.difftest.helpers.FromProdResult<T_O>, j_N: New.difftest.helpers.Json, ed1_N: New.difftest.helpers.PartialDeserializer<E1_N>, ed2_N: New.difftest.helpers.PartialDeserializer<E2_N>, cons_N: (E1_N,E2_N)->New.difftest.helpers.FromProdResult<T_N>)
        decreases j_O
        requires Old.difftest.helpers.deserializerAcceptsSubterms(ed1_O, j_O) && Old.difftest.helpers.deserializerAcceptsSubterms(ed2_O, j_O)
        requires j_N == Json_forward(j_O)
        requires ed1_N == PartialDeserializer_forward(E1_forward, E1_backward, ed1_O)
        requires ed2_N == PartialDeserializer_forward(E2_forward, E2_backward, ed2_O)
        requires forall x1_O: E1_O, x2_O: E2_O :: cons_N(E1_forward(x1_O), E2_forward(x2_O)) == FromProdResult_forward(T_forward, T_backward, cons_O(x1_O, x2_O))
        requires forall x_O: T_O :: T_backward(T_forward(x_O)) == x_O
        requires forall x_O: E1_O :: E1_backward(E1_forward(x_O)) == x_O
        requires forall x_O: E2_O :: E2_backward(E2_forward(x_O)) == x_O
        ensures New.difftest.helpers.deserializerAcceptsSubterms(ed1_N, j_N) && New.difftest.helpers.deserializerAcceptsSubterms(ed2_N, j_N)
        ensures New.difftest.helpers.deserializeTuple2Elts(j_N, ed1_N, ed2_N, cons_N) == FromProdResult_forward(T_forward, T_backward, Old.difftest.helpers.deserializeTuple2Elts(j_O, ed1_O, ed2_O, cons_O))

      lemma {:axiom} seqDeserializer_bc<T_O, T_N>(T_forward: T_O->T_N, T_backward: T_N->T_O, ed_O: Old.difftest.helpers.Deserializer<T_O>, ed_N: New.difftest.helpers.Deserializer<T_N>)
        requires ed_N == Deserializer_forward(T_forward, T_backward, ed_O)
        requires forall x_O: T_O :: T_backward(T_forward(x_O)) == x_O
        ensures New.difftest.helpers.seqDeserializer(ed_N) == Deserializer_forward((x: seq<T_O>) => Translations.MapBuiltinTypes.Seq(T_forward, x), (x: seq<T_N>) => Translations.MapBuiltinTypes.Seq(T_backward, x), Old.difftest.helpers.seqDeserializer(ed_O))

      lemma {:axiom} setDeserializer_bc<T_O, T_N>(T_forward: T_O->T_N, T_backward: T_N->T_O, ed_O: Old.difftest.helpers.Deserializer<T_O>, ed_N: New.difftest.helpers.Deserializer<T_N>)
        requires ed_N == Deserializer_forward(T_forward, T_backward, ed_O)
        requires forall x_O: T_O :: T_backward(T_forward(x_O)) == x_O
        ensures New.difftest.helpers.setDeserializer(ed_N) == Deserializer_forward((x: set<T_O>) => Translations.MapBuiltinTypes.Set(T_forward, x), (x: set<T_N>) => Translations.MapBuiltinTypes.Set(T_backward, x), Old.difftest.helpers.setDeserializer(ed_O))

      lemma {:axiom} deserializeMap_bc<V_O, V_N>(V_forward: V_O->V_N, V_backward: V_N->V_O, j_O: Old.difftest.helpers.Json, ed_O: Old.difftest.helpers.PartialDeserializer<V_O>, j_N: New.difftest.helpers.Json, ed_N: New.difftest.helpers.PartialDeserializer<V_N>)
        decreases j_O
        requires Old.difftest.helpers.deserializerAcceptsSubterms(ed_O, j_O)
        requires j_N == Json_forward(j_O)
        requires ed_N == PartialDeserializer_forward(V_forward, V_backward, ed_O)
        requires forall x_O: V_O :: V_backward(V_forward(x_O)) == x_O
        ensures New.difftest.helpers.deserializerAcceptsSubterms(ed_N, j_N)
        ensures New.difftest.helpers.deserializeMap(j_N, ed_N) == FromProdResult_forward((x: map<string,V_O>) => Translations.MapBuiltinTypes.Map((mp: string) => mp, (mp: string) => mp, V_forward, x), (x: map<string,V_N>) => Translations.MapBuiltinTypes.Map((mp: string) => mp, (mp: string) => mp, V_backward, x), Old.difftest.helpers.deserializeMap(j_O, ed_O))

      lemma {:axiom} deserializeEnum_bc<T_O, T_N>(T_forward: T_O->T_N, T_backward: T_N->T_O, j_O: Old.difftest.helpers.Json, valueMap_O: map<string,T_O>, j_N: New.difftest.helpers.Json, valueMap_N: map<string,T_N>)
        decreases j_O, valueMap_O
        requires j_N == Json_forward(j_O)
        requires valueMap_N == Translations.MapBuiltinTypes.Map((mp: string) => mp, (mp: string) => mp, T_forward, valueMap_O)
        requires forall x_O: T_O :: T_backward(T_forward(x_O)) == x_O
        ensures New.difftest.helpers.deserializeEnum(j_N, valueMap_N) == FromProdResult_forward(T_forward, T_backward, Old.difftest.helpers.deserializeEnum(j_O, valueMap_O))

      import opened def.std

      function Json_forward(J_O: Old.difftest.helpers.Json): New.difftest.helpers.Json
      {
        match J_O {
          case JsonNull() =>
            /* unchanged constructor */ New.difftest.helpers.Json.JsonNull()
          case JsonBool(b_O) =>
            /* unchanged constructor */ New.difftest.helpers.Json.JsonBool(b_O)
          case JsonInt(i_O) =>
            /* unchanged constructor */ New.difftest.helpers.Json.JsonInt(i_O)
          case JsonString(s_O) =>
            /* unchanged constructor */ New.difftest.helpers.Json.JsonString(s_O)
          case JsonArray(a_O) =>
            /* unchanged constructor */ New.difftest.helpers.Json.JsonArray(Translations.MapBuiltinTypes.Seq((sq: Old.difftest.helpers.Json) => Json_forward(sq), a_O))
          case JsonObject(o_O) =>
            /* unchanged constructor */ New.difftest.helpers.Json.JsonObject(Translations.MapBuiltinTypes.Map((mp: string) => mp, (mp: string) => mp, (mp: Old.difftest.helpers.Json) => Json_forward(mp), o_O))
        }
      }

      function Json_backward(J_N: New.difftest.helpers.Json): Old.difftest.helpers.Json
      {
        match J_N {
          case JsonNull() =>
            /* unchanged constructor */ Old.difftest.helpers.Json.JsonNull()
          case JsonBool(b_N) =>
            /* unchanged constructor */ Old.difftest.helpers.Json.JsonBool(b_N)
          case JsonInt(i_N) =>
            /* unchanged constructor */ Old.difftest.helpers.Json.JsonInt(i_N)
          case JsonString(s_N) =>
            /* unchanged constructor */ Old.difftest.helpers.Json.JsonString(s_N)
          case JsonArray(a_N) =>
            /* unchanged constructor */ Old.difftest.helpers.Json.JsonArray(Translations.MapBuiltinTypes.Seq((sq: New.difftest.helpers.Json) => Json_backward(sq), a_N))
          case JsonObject(o_N) =>
            /* unchanged constructor */ Old.difftest.helpers.Json.JsonObject(Translations.MapBuiltinTypes.Map((mp: string) => mp, (mp: string) => mp, (mp: New.difftest.helpers.Json) => Json_backward(mp), o_N))
        }
      }

      function FromProdErr_forward(F_O: Old.difftest.helpers.FromProdErr): New.difftest.helpers.FromProdErr
      {
        match F_O {
          case UnexpectedFromProdErr(desc_O) =>
            /* unchanged constructor */ New.difftest.helpers.FromProdErr.UnexpectedFromProdErr(desc_O)
          case InvalidAttrVal() =>
            /* unchanged constructor */ New.difftest.helpers.FromProdErr.InvalidAttrVal()
        }
      }

      function FromProdErr_backward(F_N: New.difftest.helpers.FromProdErr): Old.difftest.helpers.FromProdErr
      {
        match F_N {
          case UnexpectedFromProdErr(desc_N) =>
            /* unchanged constructor */ Old.difftest.helpers.FromProdErr.UnexpectedFromProdErr(desc_N)
          case InvalidAttrVal() =>
            /* unchanged constructor */ Old.difftest.helpers.FromProdErr.InvalidAttrVal()
        }
      }

      function FromProdResult_forward<T_O, T_N>(T_forward: T_O->T_N, T_backward: T_N->T_O, F_O: Old.difftest.helpers.FromProdResult<T_O>): New.difftest.helpers.FromProdResult<T_N>
      {
        Result_forward(T_forward, T_backward, (x: set<Old.difftest.helpers.FromProdErr>) => Translations.MapBuiltinTypes.Set((st: Old.difftest.helpers.FromProdErr) => FromProdErr_forward(st), x), (x: set<New.difftest.helpers.FromProdErr>) => Translations.MapBuiltinTypes.Set((st: New.difftest.helpers.FromProdErr) => FromProdErr_backward(st), x), F_O)
      }

      function FromProdResult_backward<T_O, T_N>(T_forward: T_O->T_N, T_backward: T_N->T_O, F_N: New.difftest.helpers.FromProdResult<T_N>): Old.difftest.helpers.FromProdResult<T_O>
      {
        Result_backward(T_forward, T_backward, (x: set<Old.difftest.helpers.FromProdErr>) => Translations.MapBuiltinTypes.Set((st: Old.difftest.helpers.FromProdErr) => FromProdErr_forward(st), x), (x: set<New.difftest.helpers.FromProdErr>) => Translations.MapBuiltinTypes.Set((st: New.difftest.helpers.FromProdErr) => FromProdErr_backward(st), x), F_N)
      }

      function Deserializer_forward<T_O, T_N>(T_forward: T_O->T_N, T_backward: T_N->T_O, D_O: Old.difftest.helpers.Deserializer<T_O>): New.difftest.helpers.Deserializer<T_N>
      {
        (x1_N: New.difftest.helpers.Json) => FromProdResult_forward(T_forward, T_backward, D_O(Json_backward(x1_N)))
      }

      function Deserializer_backward<T_O, T_N>(T_forward: T_O->T_N, T_backward: T_N->T_O, D_N: New.difftest.helpers.Deserializer<T_N>): Old.difftest.helpers.Deserializer<T_O>
      {
        (x1_O: Old.difftest.helpers.Json) => FromProdResult_backward(T_forward, T_backward, D_N(Json_forward(x1_O)))
      }

      function PartialDeserializer_forward<T_O, T_N>(T_forward: T_O->T_N, T_backward: T_N->T_O, P_O: Old.difftest.helpers.PartialDeserializer<T_O>): New.difftest.helpers.PartialDeserializer<T_N>
      {
        (x1_N: New.difftest.helpers.Json) => FromProdResult_forward(T_forward, T_backward, P_O(Json_backward(x1_N)))
      }

      function PartialDeserializer_backward<T_O, T_N>(T_forward: T_O->T_N, T_backward: T_N->T_O, P_N: New.difftest.helpers.PartialDeserializer<T_N>): Old.difftest.helpers.PartialDeserializer<T_O>
      {
        (x1_O: Old.difftest.helpers.Json) => FromProdResult_backward(T_forward, T_backward, P_N(Json_forward(x1_O)))
      }
    }

    module main {
      import Joint

      import Old

      import New

      import Translations

      lemma {:axiom} nameFromProdJson_bc()
        ensures Deserializer_forward((x: Joint.def.base.Name) => x, (x: Joint.def.base.Name) => x, Old.difftest.main.nameFromProdJson) == New.difftest.main.nameFromProdJson

      lemma {:axiom} entityUIDFromProdJson_bc()
        ensures Deserializer_forward((x: Joint.def.core.EntityUID) => x, (x: Joint.def.core.EntityUID) => x, Old.difftest.main.entityUIDFromProdJson) == New.difftest.main.entityUIDFromProdJson

      lemma {:axiom} policyStoreFromProdJson_bc()
        ensures Deserializer_forward((x: Joint.def.core.PolicyStore) => x, (x: Joint.def.core.PolicyStore) => x, Old.difftest.main.policyStoreFromProdJson) == New.difftest.main.policyStoreFromProdJson

      lemma typeFromProdJson_bc(j_O: Old.difftest.helpers.Json, j_N: New.difftest.helpers.Json)
        decreases j_O
        requires j_N == Json_forward(j_O)
        ensures New.difftest.main.typeFromProdJson(j_N) == FromProdResult_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), Old.difftest.main.typeFromProdJson(j_O))
      {
        var typeFromProdJsonRec := ((jr: Old.difftest.helpers.Json) requires jr < j_O => typeFromProdJson_bc(jr, Json_forward(jr));
        Old.difftest.main.typeFromProdJson(jr));
        var attrTypesFromProdJsonObjectRec := ((jr: Old.difftest.helpers.Json) requires jr < j_O => attrTypesFromProdJsonObject_bc(jr, Json_forward(jr));
        Old.difftest.main.attrTypesFromProdJsonObject(jr));
        assert New.difftest.main.typeFromProdJson(j_N) == FromProdResult_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), var (tag, body) :- (unpackJsonSum_bc(j_O, j_N);
        Old.difftest.helpers.unpackJsonSum(j_O));
        match tag {
          case "Primitive" =>
            var ty1 :- (getJsonField_bc(body, "primitiveType", Json_forward(body), "primitiveType");
            Old.difftest.helpers.getJsonField(body, "primitiveType"));
            var ty :- (deserializeEnum_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), ty1, map ["Bool" := Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool()) , "Long" := Old.validation.types.Type.Int() , "String" := Old.validation.types.Type.String()], Json_forward(ty1), map ["Bool" := New.validation.types.Type.Bool(New.validation.types.BoolType.AnyBool()) , "Long" := New.validation.types.Type.Int() , "String" := New.validation.types.Type.String()]);
            Old.difftest.helpers.deserializeEnum(ty1, map ["Bool" := Old.validation.types.Type.Bool(Old.validation.types.BoolType.AnyBool()) , "Long" := Old.validation.types.Type.Int() , "String" := Old.validation.types.Type.String()]));
            Joint.def.std.Result.Ok(ty)
          case "Set" =>
            var inner :- (deserializeField_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), body, "elementType", typeFromProdJsonRec, Json_forward(body), "elementType", (x1_N: New.difftest.helpers.Json) => FromProdResult_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), typeFromProdJsonRec(Json_backward(x1_N))));
            Old.difftest.helpers.deserializeField(body, "elementType", typeFromProdJsonRec));
            Joint.def.std.Result.Ok(Old.validation.types.Type.Set(inner))
          case "EntityOrRecord" =>
            var (tag1, body1) :- (unpackJsonSum_bc(body, Json_forward(body));
            Old.difftest.helpers.unpackJsonSum(body));
            match tag1 {
              case "Record" =>
                var attrs :- (getJsonField_bc(body1, "attrs", Json_forward(body1), "attrs");
                Old.difftest.helpers.getJsonField(body1, "attrs"));
                var attrs1 :- (deserializeField_bc((x: map<Joint.def.core.Attr,Old.validation.types.AttrType>) => Translations.MapBuiltinTypes.Map((mp: Joint.def.core.Attr) => mp, (mp: Joint.def.core.Attr) => mp, (mp: Old.validation.types.AttrType) => AttrType_forward(mp), x), (x: map<Joint.def.core.Attr,New.validation.types.AttrType>) => Translations.MapBuiltinTypes.Map((mp: Joint.def.core.Attr) => mp, (mp: Joint.def.core.Attr) => mp, (mp: New.validation.types.AttrType) => AttrType_backward(mp), x), attrs, "attrs", attrTypesFromProdJsonObjectRec, Json_forward(attrs), "attrs", (x1_N: New.difftest.helpers.Json) => FromProdResult_forward((x: map<Joint.def.core.Attr,Old.validation.types.AttrType>) => Translations.MapBuiltinTypes.Map((mp: Joint.def.core.Attr) => mp, (mp: Joint.def.core.Attr) => mp, (mp: Old.validation.types.AttrType) => AttrType_forward(mp), x), (x: map<Joint.def.core.Attr,New.validation.types.AttrType>) => Translations.MapBuiltinTypes.Map((mp: Joint.def.core.Attr) => mp, (mp: Joint.def.core.Attr) => mp, (mp: New.validation.types.AttrType) => AttrType_backward(mp), x), attrTypesFromProdJsonObjectRec(Json_backward(x1_N))));
                Old.difftest.helpers.deserializeField(attrs, "attrs", attrTypesFromProdJsonObjectRec));
                Joint.def.std.Result.Ok(Old.validation.types.Type.Record(Old.validation.types.RecordType.RecordType(attrs1, Old.validation.types.AttrsTag.ClosedAttributes())))
              case "Entity" =>
                var lub :- (deserializeField_bc((x: set<Joint.def.base.Name>) => x, (x: set<Joint.def.base.Name>) => x, body1, "lub_elements", Old.difftest.helpers.setDeserializer(Old.difftest.main.nameFromProdJson), Json_forward(body1), "lub_elements", New.difftest.helpers.setDeserializer(New.difftest.main.nameFromProdJson));
                Old.difftest.helpers.deserializeField(body1, "lub_elements", setDeserializer_bc((x: Joint.def.base.Name) => x, (x: Joint.def.base.Name) => x, Old.difftest.main.nameFromProdJson, New.difftest.main.nameFromProdJson);
                Old.difftest.helpers.setDeserializer(Old.difftest.main.nameFromProdJson)));
                Joint.def.std.Result.Ok(Old.validation.types.Type.Entity(Old.validation.types.EntityLUB.EntityLUB(set e: Joint.def.base.Name | e in lub :: Joint.def.core.EntityType.EntityType(e))))
              case _ =>
                Joint.def.std.Result.Err({Old.difftest.helpers.FromProdErr.UnexpectedFromProdErr("EntityOrRecord case " + tag)})
            }
          case "ExtensionType" =>
            var name :- (deserializeField_bc((x: Joint.def.base.Name) => x, (x: Joint.def.base.Name) => x, body, "name", Old.difftest.main.nameFromProdJson, Json_forward(body), "name", New.difftest.main.nameFromProdJson);
            Old.difftest.helpers.deserializeField(body, "name", Old.difftest.main.nameFromProdJson));
            Joint.def.std.Result.Ok(Old.validation.types.Type.Extension(name))
          case _ =>
            Joint.def.std.Result.Err({Old.difftest.helpers.FromProdErr.UnexpectedFromProdErr("Type case " + tag)})
        });
      }

      lemma attrtypeFromProdJson_bc(j_O: Old.difftest.helpers.Json, j_N: New.difftest.helpers.Json)
        decreases j_O
        requires j_N == Json_forward(j_O)
        ensures New.difftest.main.attrtypeFromProdJson(j_N) == FromProdResult_forward((x: Old.validation.types.AttrType) => AttrType_forward(x), (x: New.validation.types.AttrType) => AttrType_backward(x), Old.difftest.main.attrtypeFromProdJson(j_O))
      {
        var typeFromProdJsonRec := ((jr: Old.difftest.helpers.Json) requires jr < j_O => typeFromProdJson_bc(jr, Json_forward(jr));
        Old.difftest.main.typeFromProdJson(jr));
        assert New.difftest.main.attrtypeFromProdJson(j_N) == FromProdResult_forward((x: Old.validation.types.AttrType) => AttrType_forward(x), (x: New.validation.types.AttrType) => AttrType_backward(x), var attrType :- (deserializeField_bc((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), j_O, "attrType", typeFromProdJsonRec, j_N, "attrType", (x1_N: New.difftest.helpers.Json) => FromProdResult_forward((x: Old.validation.types.Type) => Type_forward(x), (x: New.validation.types.Type) => Type_backward(x), typeFromProdJsonRec(Json_backward(x1_N))));
        Old.difftest.helpers.deserializeField(j_O, "attrType", typeFromProdJsonRec));
        var isRequired :- (deserializeField_bc((x: bool) => x, (x: bool) => x, j_O, "isRequired", Old.difftest.helpers.getJsonBool, j_N, "isRequired", New.difftest.helpers.getJsonBool);
        Old.difftest.helpers.deserializeField(j_O, "isRequired", Old.difftest.helpers.getJsonBool));
        Joint.def.std.Result.Ok(Old.validation.types.AttrType.AttrType(attrType, isRequired)));
      }

      lemma attrTypesFromProdJsonObject_bc(j_O: Old.difftest.helpers.Json, j_N: New.difftest.helpers.Json)
        decreases j_O
        requires j_N == Json_forward(j_O)
        ensures New.difftest.main.attrTypesFromProdJsonObject(j_N) == FromProdResult_forward((x: map<Joint.def.core.Attr,Old.validation.types.AttrType>) => Translations.MapBuiltinTypes.Map((mp: Joint.def.core.Attr) => mp, (mp: Joint.def.core.Attr) => mp, (mp: Old.validation.types.AttrType) => AttrType_forward(mp), x), (x: map<Joint.def.core.Attr,New.validation.types.AttrType>) => Translations.MapBuiltinTypes.Map((mp: Joint.def.core.Attr) => mp, (mp: Joint.def.core.Attr) => mp, (mp: New.validation.types.AttrType) => AttrType_backward(mp), x), Old.difftest.main.attrTypesFromProdJsonObject(j_O))
      {
        var attrtypeFromProdJsonRec := ((jr: Old.difftest.helpers.Json) requires jr < j_O => attrtypeFromProdJson_bc(jr, Json_forward(jr));
        Old.difftest.main.attrtypeFromProdJson(jr));
        {
          deserializeMap_bc((x: Old.validation.types.AttrType) => AttrType_forward(x), (x: New.validation.types.AttrType) => AttrType_backward(x), j_O, attrtypeFromProdJsonRec, j_N, (x1_N: New.difftest.helpers.Json) => FromProdResult_forward((x: Old.validation.types.AttrType) => AttrType_forward(x), (x: New.validation.types.AttrType) => AttrType_backward(x), attrtypeFromProdJsonRec(Json_backward(x1_N))));
          assert New.difftest.main.attrTypesFromProdJsonObject(j_N) == FromProdResult_forward((x: map<Joint.def.core.Attr,Old.validation.types.AttrType>) => Translations.MapBuiltinTypes.Map((mp: Joint.def.core.Attr) => mp, (mp: Joint.def.core.Attr) => mp, (mp: Old.validation.types.AttrType) => AttrType_forward(mp), x), (x: map<Joint.def.core.Attr,New.validation.types.AttrType>) => Translations.MapBuiltinTypes.Map((mp: Joint.def.core.Attr) => mp, (mp: Joint.def.core.Attr) => mp, (mp: New.validation.types.AttrType) => AttrType_backward(mp), x), Old.difftest.helpers.deserializeMap(j_O, attrtypeFromProdJsonRec));
        }
      }

      lemma entityTypePairFromProdJson_bc(j_O: Old.difftest.helpers.Json, j_N: New.difftest.helpers.Json)
        decreases j_O
        requires j_N == Json_forward(j_O)
        ensures New.difftest.main.entityTypePairFromProdJson(j_N) == FromProdResult_forward((x: (Joint.def.core.EntityType,Old.validation.validator.TypecheckerEntityType)) => (x.0, TypecheckerEntityType_forward(x.1)), (x: (Joint.def.core.EntityType,New.validation.validator.TypecheckerEntityType)) => (x.0, TypecheckerEntityType_backward(x.1)), Old.difftest.main.entityTypePairFromProdJson(j_O))
      {
        deserializeTuple2Elts_bc((x: (Joint.def.core.EntityType,Old.validation.validator.TypecheckerEntityType)) => (x.0, TypecheckerEntityType_forward(x.1)), (x: (Joint.def.core.EntityType,New.validation.validator.TypecheckerEntityType)) => (x.0, TypecheckerEntityType_backward(x.1)), (x: Joint.def.base.Name) => x, (x: Joint.def.base.Name) => x, (x: Old.validation.validator.TypecheckerEntityType) => TypecheckerEntityType_forward(x), (x: New.validation.validator.TypecheckerEntityType) => TypecheckerEntityType_backward(x), j_O, Old.difftest.main.nameFromProdJson, (data: Old.difftest.helpers.Json) => var descendants :- Old.difftest.helpers.deserializeField(data, "descendants", Old.difftest.helpers.setDeserializer(Old.difftest.main.nameFromProdJson));
        var descendants1 := set e: Joint.def.base.Name | e in descendants :: Joint.def.core.EntityType.EntityType(e);
        var attrs :- Old.difftest.helpers.getJsonField(data, "attributes");
        var attrs1 :- Old.difftest.helpers.deserializeField(attrs, "attrs", Old.difftest.main.attrTypesFromProdJsonObject);
        Joint.def.std.Result.Ok(Old.validation.validator.TypecheckerEntityType.TypecheckerEntityType(descendants1, attrs1)), (ty: Joint.def.base.Name, et: Old.validation.validator.TypecheckerEntityType) => Joint.def.std.Result.Ok((Joint.def.core.EntityType.EntityType(ty), et)), j_N, New.difftest.main.nameFromProdJson, (data: New.difftest.helpers.Json) => var descendants :- New.difftest.helpers.deserializeField(data, "descendants", New.difftest.helpers.setDeserializer(New.difftest.main.nameFromProdJson));
        var descendants1 := set e: Joint.def.base.Name | e in descendants :: Joint.def.core.EntityType.EntityType(e);
        var attrs :- New.difftest.helpers.getJsonField(data, "attributes");
        var attrs1 :- New.difftest.helpers.deserializeField(attrs, "attrs", New.difftest.main.attrTypesFromProdJsonObject);
        Joint.def.std.Result.Ok(New.validation.validator.TypecheckerEntityType.TypecheckerEntityType(descendants1, attrs1)), (ty: Joint.def.base.Name, et: New.validation.validator.TypecheckerEntityType) => Joint.def.std.Result.Ok((Joint.def.core.EntityType.EntityType(ty), et)));
        assert New.difftest.main.entityTypePairFromProdJson(j_N) == FromProdResult_forward((x: (Joint.def.core.EntityType,Old.validation.validator.TypecheckerEntityType)) => (x.0, TypecheckerEntityType_forward(x.1)), (x: (Joint.def.core.EntityType,New.validation.validator.TypecheckerEntityType)) => (x.0, TypecheckerEntityType_backward(x.1)), Old.difftest.helpers.deserializeTuple2Elts(j_O, Old.difftest.main.nameFromProdJson, (data: Old.difftest.helpers.Json) => var descendants :- (deserializeField_bc((x: set<Joint.def.base.Name>) => x, (x: set<Joint.def.base.Name>) => x, data, "descendants", Old.difftest.helpers.setDeserializer(Old.difftest.main.nameFromProdJson), Json_forward(data), "descendants", New.difftest.helpers.setDeserializer(New.difftest.main.nameFromProdJson));
        Old.difftest.helpers.deserializeField(data, "descendants", setDeserializer_bc((x: Joint.def.base.Name) => x, (x: Joint.def.base.Name) => x, Old.difftest.main.nameFromProdJson, New.difftest.main.nameFromProdJson);
        Old.difftest.helpers.setDeserializer(Old.difftest.main.nameFromProdJson)));
        var descendants1 := set e: Joint.def.base.Name | e in descendants :: Joint.def.core.EntityType.EntityType(e);
        var attrs :- (getJsonField_bc(data, "attributes", Json_forward(data), "attributes");
        Old.difftest.helpers.getJsonField(data, "attributes"));
        var attrs1 :- (deserializeField_bc((x: map<Joint.def.core.Attr,Old.validation.types.AttrType>) => Translations.MapBuiltinTypes.Map((mp: Joint.def.core.Attr) => mp, (mp: Joint.def.core.Attr) => mp, (mp: Old.validation.types.AttrType) => AttrType_forward(mp), x), (x: map<Joint.def.core.Attr,New.validation.types.AttrType>) => Translations.MapBuiltinTypes.Map((mp: Joint.def.core.Attr) => mp, (mp: Joint.def.core.Attr) => mp, (mp: New.validation.types.AttrType) => AttrType_backward(mp), x), attrs, "attrs", Old.difftest.main.attrTypesFromProdJsonObject, Json_forward(attrs), "attrs", New.difftest.main.attrTypesFromProdJsonObject);
        Old.difftest.helpers.deserializeField(attrs, "attrs", Old.difftest.main.attrTypesFromProdJsonObject));
        Joint.def.std.Result.Ok(Old.validation.validator.TypecheckerEntityType.TypecheckerEntityType(descendants1, attrs1)), (ty: Joint.def.base.Name, et: Old.validation.validator.TypecheckerEntityType) => Joint.def.std.Result.Ok((Joint.def.core.EntityType.EntityType(ty), et))));
      }

      lemma {:axiom} applySpecFromProdJson_bc(j_O: Old.difftest.helpers.Json, j_N: New.difftest.helpers.Json)
        decreases j_O
        requires j_N == Json_forward(j_O)
        ensures New.difftest.main.applySpecFromProdJson(j_N) == FromProdResult_forward((x: Old.validation.validator.TypecheckerApplySpec) => TypecheckerApplySpec_forward(x), (x: New.validation.validator.TypecheckerApplySpec) => TypecheckerApplySpec_backward(x), Old.difftest.main.applySpecFromProdJson(j_O))

      lemma actionIdPairFromProdJson_bc(j_O: Old.difftest.helpers.Json, j_N: New.difftest.helpers.Json)
        decreases j_O
        requires j_N == Json_forward(j_O)
        ensures New.difftest.main.actionIdPairFromProdJson(j_N) == FromProdResult_forward((x: (Joint.def.core.EntityUID,Old.validation.validator.TypecheckerActionId)) => (x.0, TypecheckerActionId_forward(x.1)), (x: (Joint.def.core.EntityUID,New.validation.validator.TypecheckerActionId)) => (x.0, TypecheckerActionId_backward(x.1)), Old.difftest.main.actionIdPairFromProdJson(j_O))
      {
        deserializeTuple2Elts_bc((x: (Joint.def.core.EntityUID,Old.validation.validator.TypecheckerActionId)) => (x.0, TypecheckerActionId_forward(x.1)), (x: (Joint.def.core.EntityUID,New.validation.validator.TypecheckerActionId)) => (x.0, TypecheckerActionId_backward(x.1)), (x: Joint.def.core.EntityUID) => x, (x: Joint.def.core.EntityUID) => x, (x: Old.validation.validator.TypecheckerActionId) => TypecheckerActionId_forward(x), (x: New.validation.validator.TypecheckerActionId) => TypecheckerActionId_backward(x), j_O, Old.difftest.main.entityUIDFromProdJson, (data: Old.difftest.helpers.Json) => var appliesTo :- Old.difftest.helpers.deserializeField(data, "appliesTo", Old.difftest.main.applySpecFromProdJson);
        var descendants :- Old.difftest.helpers.deserializeField(data, "descendants", Old.difftest.helpers.setDeserializer(Old.difftest.main.entityUIDFromProdJson));
        var context :- Old.difftest.helpers.getJsonField(data, "context");
        var context1 :- Old.difftest.helpers.deserializeField(context, "attrs", Old.difftest.main.attrTypesFromProdJsonObject);
        Joint.def.std.Result.Ok(Old.validation.validator.TypecheckerActionId.TypecheckerActionId(appliesTo, descendants, context1)), (uid: Joint.def.core.EntityUID, act: Old.validation.validator.TypecheckerActionId) => Joint.def.std.Result.Ok((uid, act)), j_N, New.difftest.main.entityUIDFromProdJson, (data: New.difftest.helpers.Json) => var appliesTo :- New.difftest.helpers.deserializeField(data, "appliesTo", New.difftest.main.applySpecFromProdJson);
        var descendants :- New.difftest.helpers.deserializeField(data, "descendants", New.difftest.helpers.setDeserializer(New.difftest.main.entityUIDFromProdJson));
        var context :- New.difftest.helpers.getJsonField(data, "context");
        var context1 :- New.difftest.helpers.deserializeField(context, "attrs", New.difftest.main.attrTypesFromProdJsonObject);
        Joint.def.std.Result.Ok(New.validation.validator.TypecheckerActionId.TypecheckerActionId(appliesTo, descendants, context1)), (uid: Joint.def.core.EntityUID, act: New.validation.validator.TypecheckerActionId) => Joint.def.std.Result.Ok((uid, act)));
        assert New.difftest.main.actionIdPairFromProdJson(j_N) == FromProdResult_forward((x: (Joint.def.core.EntityUID,Old.validation.validator.TypecheckerActionId)) => (x.0, TypecheckerActionId_forward(x.1)), (x: (Joint.def.core.EntityUID,New.validation.validator.TypecheckerActionId)) => (x.0, TypecheckerActionId_backward(x.1)), Old.difftest.helpers.deserializeTuple2Elts(j_O, Old.difftest.main.entityUIDFromProdJson, (data: Old.difftest.helpers.Json) => var appliesTo :- (deserializeField_bc((x: Old.validation.validator.TypecheckerApplySpec) => TypecheckerApplySpec_forward(x), (x: New.validation.validator.TypecheckerApplySpec) => TypecheckerApplySpec_backward(x), data, "appliesTo", Old.difftest.main.applySpecFromProdJson, Json_forward(data), "appliesTo", New.difftest.main.applySpecFromProdJson);
        Old.difftest.helpers.deserializeField(data, "appliesTo", Old.difftest.main.applySpecFromProdJson));
        var descendants :- (deserializeField_bc((x: set<Joint.def.core.EntityUID>) => x, (x: set<Joint.def.core.EntityUID>) => x, data, "descendants", Old.difftest.helpers.setDeserializer(Old.difftest.main.entityUIDFromProdJson), Json_forward(data), "descendants", New.difftest.helpers.setDeserializer(New.difftest.main.entityUIDFromProdJson));
        Old.difftest.helpers.deserializeField(data, "descendants", setDeserializer_bc((x: Joint.def.core.EntityUID) => x, (x: Joint.def.core.EntityUID) => x, Old.difftest.main.entityUIDFromProdJson, New.difftest.main.entityUIDFromProdJson);
        Old.difftest.helpers.setDeserializer(Old.difftest.main.entityUIDFromProdJson)));
        var context :- (getJsonField_bc(data, "context", Json_forward(data), "context");
        Old.difftest.helpers.getJsonField(data, "context"));
        var context1 :- (deserializeField_bc((x: map<Joint.def.core.Attr,Old.validation.types.AttrType>) => Translations.MapBuiltinTypes.Map((mp: Joint.def.core.Attr) => mp, (mp: Joint.def.core.Attr) => mp, (mp: Old.validation.types.AttrType) => AttrType_forward(mp), x), (x: map<Joint.def.core.Attr,New.validation.types.AttrType>) => Translations.MapBuiltinTypes.Map((mp: Joint.def.core.Attr) => mp, (mp: Joint.def.core.Attr) => mp, (mp: New.validation.types.AttrType) => AttrType_backward(mp), x), context, "attrs", Old.difftest.main.attrTypesFromProdJsonObject, Json_forward(context), "attrs", New.difftest.main.attrTypesFromProdJsonObject);
        Old.difftest.helpers.deserializeField(context, "attrs", Old.difftest.main.attrTypesFromProdJsonObject));
        Joint.def.std.Result.Ok(Old.validation.validator.TypecheckerActionId.TypecheckerActionId(appliesTo, descendants, context1)), (uid: Joint.def.core.EntityUID, act: Old.validation.validator.TypecheckerActionId) => Joint.def.std.Result.Ok((uid, act))));
      }

      lemma validatorFromProdJson_bc()
        ensures Deserializer_forward((x: (Joint.def.core.PolicyStore,Old.validation.validator.Validator)) => (x.0, Validator_forward(x.1)), (x: (Joint.def.core.PolicyStore,New.validation.validator.Validator)) => (x.0, Validator_backward(x.1)), Old.difftest.main.validatorFromProdJson) == New.difftest.main.validatorFromProdJson
      {}

      lemma typeErrorToString_bc(e_O: Old.validation.types.TypeError, e_N: New.validation.types.TypeError)
        decreases e_O
        requires e_N == TypeError_forward(e_O)
        ensures New.difftest.main.typeErrorToString(e_N) == Old.difftest.main.typeErrorToString(e_O)
      {
        match e_O {
          case LubErr(_, _) =>
            assert New.difftest.main.typeErrorToString(e_N) == "LubErr";
          case SubtyErr(_, _) =>
            assert New.difftest.main.typeErrorToString(e_N) == "SubtyErr";
          case UnexpectedType(_) =>
            assert New.difftest.main.typeErrorToString(e_N) == "UnexpectedType";
          case AttrNotFound(_, _) =>
            assert New.difftest.main.typeErrorToString(e_N) == "AttrNotFound";
          case UnknownEntities(_) =>
            assert New.difftest.main.typeErrorToString(e_N) == "UnknownEntities";
          case ExtensionErr(_) =>
            assert New.difftest.main.typeErrorToString(e_N) == "ExtensionErr";
          case EmptyLUB() =>
            assert New.difftest.main.typeErrorToString(e_N) == "EmptyLUB";
        }
      }

      lemma validationErrorToString_bc(e_O: Old.validation.validator.ValidationError, e_N: New.validation.validator.ValidationError)
        decreases e_O
        requires e_N == ValidationError_forward(e_O)
        ensures New.difftest.main.validationErrorToString(e_N) == Old.difftest.main.validationErrorToString(e_O)
      {
        match e_O {
          case AllFalse() =>
            assert New.difftest.main.validationErrorToString(e_N) == "AllFalse";
          case StrictTypeError(e1) =>
            assert New.difftest.main.validationErrorToString(e_N) == Old.difftest.main.strictTypeErrorToString(e1);
        }
      }

      import opened def.base

      import opened def.core

      import opened def.engine

      import opened def.std

      import opened def.templates

      import opened def.ext.fun

      import opened restrictedExpr

      import opened validation.types

      import opened validation.validator

      import opened helpers

      function ScopeDeserializers_forward(S_O: Old.difftest.main.ScopeDeserializers): New.difftest.main.ScopeDeserializers
      {
        match S_O {
          case ScopeDeserializers(slotId_O) =>
            /* unchanged constructor */ New.difftest.main.ScopeDeserializers.ScopeDeserializers(slotId_O)
        }
      }

      function ScopeDeserializers_backward(S_N: New.difftest.main.ScopeDeserializers): Old.difftest.main.ScopeDeserializers
      {
        match S_N {
          case ScopeDeserializers(slotId_N) =>
            /* unchanged constructor */ Old.difftest.main.ScopeDeserializers.ScopeDeserializers(slotId_N)
        }
      }
    }

    module restrictedExpr {
      import Joint

      import Old

      import New

      import Translations

      import opened def.core

      import opened def.base

      import ext = def.ext.fun

      import opened def.engine

      import opened def.std
    }
  }

  module test {
    import Joint

    import Old

    import New

    import Translations

    module decimal {
      import Joint

      import Old

      import New

      import Translations

      import opened def.ext.decimal.parseDecimal
    }

    module ipaddr {
      import Joint

      import Old

      import New

      import Translations

      import opened def.ext.ipaddr.parseIPAddr
    }
  }

  module def {
    import Joint

    import Old

    import New

    import Translations

    module util {
      import Joint

      import Old

      import New

      import Translations

      import opened base

      import opened core
    }

    module core {
      import Joint

      import Old

      import New

      import Translations

      import opened base

      import ext
    }

    module ext {
      import Joint

      import Old

      import New

      import Translations

      import opened base

      import opened fun

      import dec = decimal

      import ip = ipaddr

      module decimal {
        import Joint

        import Old

        import New

        import Translations

        import opened base

        import opened fun

        import opened core

        import opened parseDecimal

        function Coercions_forward<T_O(==)(!new), T_N(==)(!new)>(T_forward: T_O->T_N, T_backward: T_N->T_O, C_O: Joint.def.ext.decimal.Coercions<T_O>): Joint.def.ext.decimal.Coercions<T_N>
        {
          fun.Coercions_forward((x: Joint.def.ext.decimal.Decimal) => x, (x: Joint.def.ext.decimal.Decimal) => x, T_forward, T_backward, C_O)
        }

        function Coercions_backward<T_O(==)(!new), T_N(==)(!new)>(T_forward: T_O->T_N, T_backward: T_N->T_O, C_N: Joint.def.ext.decimal.Coercions<T_N>): Joint.def.ext.decimal.Coercions<T_O>
        {
          fun.Coercions_backward((x: Joint.def.ext.decimal.Decimal) => x, (x: Joint.def.ext.decimal.Decimal) => x, T_forward, T_backward, C_N)
        }

        function DecimalFunctions_forward<T_O(==)(!new), T_N(==)(!new)>(T_forward: T_O->T_N, T_backward: T_N->T_O, D_O: Joint.def.ext.decimal.DecimalFunctions<T_O>): Joint.def.ext.decimal.DecimalFunctions<T_N>
        {
          match D_O {
            case DecimalFunctions(coerce_O) =>
              /* unchanged constructor */ Joint.def.ext.decimal.DecimalFunctions.DecimalFunctions(Coercions_forward(T_forward, T_backward, coerce_O))
          }
        }

        function DecimalFunctions_backward<T_O(==)(!new), T_N(==)(!new)>(T_forward: T_O->T_N, T_backward: T_N->T_O, D_N: Joint.def.ext.decimal.DecimalFunctions<T_N>): Joint.def.ext.decimal.DecimalFunctions<T_O>
        {
          match D_N {
            case DecimalFunctions(coerce_N) =>
              /* unchanged constructor */ Joint.def.ext.decimal.DecimalFunctions.DecimalFunctions(Coercions_backward(T_forward, T_backward, coerce_N))
          }
        }

        module core {
          import Joint

          import Old

          import New

          import Translations
        }

        module parseDecimal {
          import Joint

          import Old

          import New

          import Translations

          import opened utils.parser

          import opened std

          import opened core
        }
      }

      module ipaddr {
        import Joint

        import Old

        import New

        import Translations

        import opened base

        import opened fun

        import opened core

        import opened parseIPAddr

        function Coercions_forward<T_O(==)(!new), T_N(==)(!new)>(T_forward: T_O->T_N, T_backward: T_N->T_O, C_O: Joint.def.ext.ipaddr.Coercions<T_O>): Joint.def.ext.ipaddr.Coercions<T_N>
        {
          fun.Coercions_forward((x: Joint.def.ext.ipaddr.IPAddr) => x, (x: Joint.def.ext.ipaddr.IPAddr) => x, T_forward, T_backward, C_O)
        }

        function Coercions_backward<T_O(==)(!new), T_N(==)(!new)>(T_forward: T_O->T_N, T_backward: T_N->T_O, C_N: Joint.def.ext.ipaddr.Coercions<T_N>): Joint.def.ext.ipaddr.Coercions<T_O>
        {
          fun.Coercions_backward((x: Joint.def.ext.ipaddr.IPAddr) => x, (x: Joint.def.ext.ipaddr.IPAddr) => x, T_forward, T_backward, C_N)
        }

        function IPAddrFunctions_forward<T_O(==)(!new), T_N(==)(!new)>(T_forward: T_O->T_N, T_backward: T_N->T_O, I_O: Joint.def.ext.ipaddr.IPAddrFunctions<T_O>): Joint.def.ext.ipaddr.IPAddrFunctions<T_N>
        {
          match I_O {
            case IPAddrFunctions(coerce_O) =>
              /* unchanged constructor */ Joint.def.ext.ipaddr.IPAddrFunctions.IPAddrFunctions(Coercions_forward(T_forward, T_backward, coerce_O))
          }
        }

        function IPAddrFunctions_backward<T_O(==)(!new), T_N(==)(!new)>(T_forward: T_O->T_N, T_backward: T_N->T_O, I_N: Joint.def.ext.ipaddr.IPAddrFunctions<T_N>): Joint.def.ext.ipaddr.IPAddrFunctions<T_O>
        {
          match I_N {
            case IPAddrFunctions(coerce_N) =>
              /* unchanged constructor */ Joint.def.ext.ipaddr.IPAddrFunctions.IPAddrFunctions(Coercions_backward(T_forward, T_backward, coerce_N))
          }
        }

        module core {
          import Joint

          import Old

          import New

          import Translations
        }

        module parseIPAddr {
          import Joint

          import Old

          import New

          import Translations

          import opened utils.parser

          import opened std

          import opened core
        }
      }

      module fun {
        import Joint

        import Old

        import New

        import Translations

        import opened base

        function ExtFun_forward<T_O(==)(!new), T_N(==)(!new)>(T_forward: T_O->T_N, T_backward: T_N->T_O, E_O: Joint.def.ext.fun.ExtFun<T_O>): Joint.def.ext.fun.ExtFun<T_N>
        {
          match E_O {
            case ExtFun(fun_O) =>
              /* unchanged constructor */ Joint.def.ext.fun.ExtFun.ExtFun((x1_N: seq<T_N>) => Result_forward(T_forward, T_backward, fun_O(Translations.MapBuiltinTypes.Seq(T_backward, x1_N))))
          }
        }

        function ExtFun_backward<T_O(==)(!new), T_N(==)(!new)>(T_forward: T_O->T_N, T_backward: T_N->T_O, E_N: Joint.def.ext.fun.ExtFun<T_N>): Joint.def.ext.fun.ExtFun<T_O>
        {
          match E_N {
            case ExtFun(fun_N) =>
              /* unchanged constructor */ Joint.def.ext.fun.ExtFun.ExtFun((x1_O: seq<T_O>) => Result_backward(T_forward, T_backward, fun_N(Translations.MapBuiltinTypes.Seq(T_forward, x1_O))))
          }
        }

        function Coercions_forward<E_O(==)(!new), E_N(==)(!new), T_O(==)(!new), T_N(==)(!new)>(E_forward: E_O->E_N, E_backward: E_N->E_O, T_forward: T_O->T_N, T_backward: T_N->T_O, C_O: Joint.def.ext.fun.Coercions<E_O,T_O>): Joint.def.ext.fun.Coercions<E_N,T_N>
        {
          match C_O {
            case Coercions(Bool_O, Int_O, String_O, Ext_O) =>
              /* unchanged constructor */ Joint.def.ext.fun.Coercions.Coercions(Coerce_forward((x: bool) => x, (x: bool) => x, T_forward, T_backward, Bool_O), Coerce_forward((x: int) => x, (x: int) => x, T_forward, T_backward, Int_O), Coerce_forward((x: string) => x, (x: string) => x, T_forward, T_backward, String_O), Coerce_forward(E_forward, E_backward, T_forward, T_backward, Ext_O))
          }
        }

        function Coercions_backward<E_O(==)(!new), E_N(==)(!new), T_O(==)(!new), T_N(==)(!new)>(E_forward: E_O->E_N, E_backward: E_N->E_O, T_forward: T_O->T_N, T_backward: T_N->T_O, C_N: Joint.def.ext.fun.Coercions<E_N,T_N>): Joint.def.ext.fun.Coercions<E_O,T_O>
        {
          match C_N {
            case Coercions(Bool_N, Int_N, String_N, Ext_N) =>
              /* unchanged constructor */ Joint.def.ext.fun.Coercions.Coercions(Coerce_backward((x: bool) => x, (x: bool) => x, T_forward, T_backward, Bool_N), Coerce_backward((x: int) => x, (x: int) => x, T_forward, T_backward, Int_N), Coerce_backward((x: string) => x, (x: string) => x, T_forward, T_backward, String_N), Coerce_backward(E_forward, E_backward, T_forward, T_backward, Ext_N))
          }
        }
      }

      module utils {
        import Joint

        import Old

        import New

        import Translations

        module parser {
          import Joint

          import Old

          import New

          import Translations

          import opened std
        }
      }
    }

    module base {
      import Joint

      import Old

      import New

      import Translations

      import opened std

      function Result_forward<T_O, T_N>(T_forward: T_O->T_N, T_backward: T_N->T_O, R_O: Joint.def.base.Result<T_O>): Joint.def.base.Result<T_N>
      {
        std.Result_forward(T_forward, T_backward, (x: Joint.def.base.Error) => x, (x: Joint.def.base.Error) => x, R_O)
      }

      function Result_backward<T_O, T_N>(T_forward: T_O->T_N, T_backward: T_N->T_O, R_N: Joint.def.base.Result<T_N>): Joint.def.base.Result<T_O>
      {
        std.Result_backward(T_forward, T_backward, (x: Joint.def.base.Error) => x, (x: Joint.def.base.Error) => x, R_N)
      }

      function Coerce_forward<Base_O(==)(!new), Base_N(==)(!new), Wrapper_O(==)(!new), Wrapper_N(==)(!new)>(Base_forward: Base_O->Base_N, Base_backward: Base_N->Base_O, Wrapper_forward: Wrapper_O->Wrapper_N, Wrapper_backward: Wrapper_N->Wrapper_O, C_O: Joint.def.base.Coerce<Base_O,Wrapper_O>): Joint.def.base.Coerce<Base_N,Wrapper_N>
      {
        match C_O {
          case Coerce(wrap_O, unwrap_O) =>
            /* unchanged constructor */ Joint.def.base.Coerce.Coerce((x1_N: Base_N) => Wrapper_forward(wrap_O(Base_backward(x1_N))), (x1_N: Wrapper_N) => Result_forward(Base_forward, Base_backward, unwrap_O(Wrapper_backward(x1_N))))
        }
      }

      function Coerce_backward<Base_O(==)(!new), Base_N(==)(!new), Wrapper_O(==)(!new), Wrapper_N(==)(!new)>(Base_forward: Base_O->Base_N, Base_backward: Base_N->Base_O, Wrapper_forward: Wrapper_O->Wrapper_N, Wrapper_backward: Wrapper_N->Wrapper_O, C_N: Joint.def.base.Coerce<Base_N,Wrapper_N>): Joint.def.base.Coerce<Base_O,Wrapper_O>
      {
        match C_N {
          case Coerce(wrap_N, unwrap_N) =>
            /* unchanged constructor */ Joint.def.base.Coerce.Coerce((x1_O: Base_O) => Wrapper_backward(wrap_N(Base_forward(x1_O))), (x1_O: Wrapper_O) => Result_backward(Base_forward, Base_backward, unwrap_N(Wrapper_forward(x1_O))))
        }
      }
    }

    module engine {
      import Joint

      import Old

      import New

      import Translations

      import opened base

      import opened core

      import opened wildcard

      module wildcard {
        import Joint

        import Old

        import New

        import Translations

        import opened core

        import opened std

        import opened lib = core
      }
    }

    module templates {
      import Joint

      import Old

      import New

      import Translations

      import opened core
    }

    module std {
      import Joint

      import Old

      import New

      import Translations

      function Option_forward<T_O, T_N>(T_forward: T_O->T_N, T_backward: T_N->T_O, O_O: Joint.def.std.Option<T_O>): Joint.def.std.Option<T_N>
      {
        match O_O {
          case Some(value_O) =>
            /* unchanged constructor */ Joint.def.std.Option.Some(T_forward(value_O))
          case None() =>
            /* unchanged constructor */ Joint.def.std.Option.None()
        }
      }

      function Option_backward<T_O, T_N>(T_forward: T_O->T_N, T_backward: T_N->T_O, O_N: Joint.def.std.Option<T_N>): Joint.def.std.Option<T_O>
      {
        match O_N {
          case Some(value_N) =>
            /* unchanged constructor */ Joint.def.std.Option.Some(T_backward(value_N))
          case None() =>
            /* unchanged constructor */ Joint.def.std.Option.None()
        }
      }

      function Result_forward<T_O, T_N, E_O, E_N>(T_forward: T_O->T_N, T_backward: T_N->T_O, E_forward: E_O->E_N, E_backward: E_N->E_O, R_O: Joint.def.std.Result<T_O,E_O>): Joint.def.std.Result<T_N,E_N>
      {
        match R_O {
          case Ok(value_O) =>
            /* unchanged constructor */ Joint.def.std.Result.Ok(T_forward(value_O))
          case Err(error_O) =>
            /* unchanged constructor */ Joint.def.std.Result.Err(E_forward(error_O))
        }
      }

      function Result_backward<T_O, T_N, E_O, E_N>(T_forward: T_O->T_N, T_backward: T_N->T_O, E_forward: E_O->E_N, E_backward: E_N->E_O, R_N: Joint.def.std.Result<T_N,E_N>): Joint.def.std.Result<T_O,E_O>
      {
        match R_N {
          case Ok(value_N) =>
            /* unchanged constructor */ Joint.def.std.Result.Ok(T_backward(value_N))
          case Err(error_N) =>
            /* unchanged constructor */ Joint.def.std.Result.Err(E_backward(error_N))
        }
      }
    }
  }

  module pslicing {
    import Joint

    import Old

    import New

    import Translations

    import opened def.base

    import opened def.core

    import opened def.engine

    import opened def.std

    import opened slicing

    import opened eval.basic
  }

  module basic {
    import Joint

    import Old

    import New

    import Translations

    import opened def.base

    import opened def.core

    import opened def.engine
  }

  module slicing {
    import Joint

    import Old

    import New

    import Translations

    import opened def.base

    import opened def.core

    import opened def.engine
  }
}
