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

      import opened def.base

      import opened def.core

      import opened def.engine
    }

    module types {
      import Joint

      import Old

      import New

      import Translations

      import opened def.base

      import opened def.core

      function Result_forward<T_O, T_N>(T_forward: T_O->T_N, T_backward: T_N->T_O, R_O: Joint.validation.types.Result<T_O>): Joint.validation.types.Result<T_N>
      {
        std.Result_forward(T_forward, T_backward, (x: Joint.validation.types.TypeError) => x, (x: Joint.validation.types.TypeError) => x, R_O)
      }

      function Result_backward<T_O, T_N>(T_forward: T_O->T_N, T_backward: T_N->T_O, R_N: Joint.validation.types.Result<T_N>): Joint.validation.types.Result<T_O>
      {
        std.Result_backward(T_forward, T_backward, (x: Joint.validation.types.TypeError) => x, (x: Joint.validation.types.TypeError) => x, R_N)
      }

      function Option_forward<T_O, T_N>(T_forward: T_O->T_N, T_backward: T_N->T_O, O_O: Joint.validation.types.Option<T_O>): Joint.validation.types.Option<T_N>
      {
        std.Option_forward(T_forward, T_backward, O_O)
      }

      function Option_backward<T_O, T_N>(T_forward: T_O->T_N, T_backward: T_N->T_O, O_N: Joint.validation.types.Option<T_N>): Joint.validation.types.Option<T_O>
      {
        std.Option_backward(T_forward, T_backward, O_N)
      }
    }

    module subtyping {
      import Joint

      import Old

      import New

      import Translations

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
    }

    module ext {
      import Joint

      import Old

      import New

      import Translations

      import opened def.base

      import opened types

      module decimal {
        import Joint

        import Old

        import New

        import Translations

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

        import opened def.std

        import opened def.base

        import opened def.core

        import opened def.ext.ipaddr.parseIPAddr

        import opened types
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

        import opened def.base

        import opened def.core

        import opened def.engine

        import opened types

        import opened subtyping

        import opened typechecker
      }

      module strict_inf_strict {
        import Joint

        import Old

        import New

        import Translations

        import opened typechecker

        import opened types

        import opened subtyping

        import opened base

        import opened model

        import opened soundness

        import opened def.core

        import opened def.engine

        import opened ext
      }

      module model {
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

        import opened base

        import opened ext
      }

      module toplevel {
        import Joint

        import Old

        import New

        import Translations

        import opened typechecker

        import opened types

        import opened subtyping

        import opened base

        import opened model

        import opened soundness

        import opened strict__soundness = strict_soundness

        import opened def.core

        import opened def.engine

        import opened ext
      }

      module strict_soundness {
        import Joint

        import Old

        import New

        import Translations

        import opened typechecker

        import opened types

        import opened subtyping

        import opened base

        import opened model

        import opened soundness

        import opened def.core

        import opened def.engine

        import opened ext
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

        function Result_forward<T_O, T_N>(T_forward: T_O->T_N, T_backward: T_N->T_O, R_O: Joint.validation.thm.soundness.Result<T_O>): Joint.validation.thm.soundness.Result<T_N>
        {
          types.Result_forward(T_forward, T_backward, R_O)
        }

        function Result_backward<T_O, T_N>(T_forward: T_O->T_N, T_backward: T_N->T_O, R_N: Joint.validation.thm.soundness.Result<T_N>): Joint.validation.thm.soundness.Result<T_O>
        {
          types.Result_backward(T_forward, T_backward, R_N)
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

      lemma {:axiom} getJsonField_bc(j_O: Old.difftest.helpers.Json, f_O: string, j_N: New.difftest.helpers.Json, f_N: string)
        decreases j_O, f_O
        requires j_N == Json_forward(j_O)
        requires f_N == f_O
        ensures New.difftest.helpers.getJsonField(j_N, f_N) == FromProdResult_forward((x: Old.difftest.helpers.Json) => Json_forward(x), (x: New.difftest.helpers.Json) => Json_backward(x), Old.difftest.helpers.getJsonField(j_O, f_O))

      lemma {:axiom} deserializeField_bc<F_O, F_N>(F_forward: F_O->F_N, F_backward: F_N->F_O, j_O: Old.difftest.helpers.Json, fn_O: string, fd_O: Old.difftest.helpers.PartialDeserializer<F_O>, j_N: New.difftest.helpers.Json, fn_N: string, fd_N: New.difftest.helpers.PartialDeserializer<F_N>)
        decreases j_O, fn_O
        requires Old.difftest.helpers.deserializerAcceptsSubterms(fd_O, j_O)
        requires j_N == Json_forward(j_O)
        requires fn_N == fn_O
        requires fd_N == PartialDeserializer_forward(F_forward, F_backward, fd_O)
        requires forall x_O: F_O :: F_backward(F_forward(x_O)) == x_O
        ensures New.difftest.helpers.deserializerAcceptsSubterms(fd_N, j_N)
        ensures New.difftest.helpers.deserializeField(j_N, fn_N, fd_N) == FromProdResult_forward(F_forward, F_backward, Old.difftest.helpers.deserializeField(j_O, fn_O, fd_O))

      lemma {:axiom} deserializeField_2_difftest_main_attrTypesFromProdJsonObject_bc<F_O, F_N>(F_forward: F_O->F_N, F_backward: F_N->F_O, j_O: Old.difftest.helpers.Json, fn_O: string, j_N: New.difftest.helpers.Json, fn_N: string)
        decreases j_O, fn_O
        requires Old.difftest.helpers.deserializerAcceptsSubterms(Old.difftest.main.attrTypesFromProdJsonObject, j_O)
        requires j_N == Json_forward(j_O)
        requires fn_N == fn_O
        requires forall x_O: F_O :: F_backward(F_forward(x_O)) == x_O
        ensures New.difftest.helpers.deserializerAcceptsSubterms(New.difftest.main.attrTypesFromProdJsonObject, j_N)
        ensures New.difftest.helpers.deserializeField(j_N, fn_N, New.difftest.main.attrTypesFromProdJsonObject) == FromProdResult_forward((x: map<Joint.def.core.Attr,Joint.validation.types.AttrType>) => x, (x: map<Joint.def.core.Attr,Joint.validation.types.AttrType>) => x, Old.difftest.helpers.deserializeField(j_O, fn_O, Old.difftest.main.attrTypesFromProdJsonObject))

      lemma deserializeField_2_difftest_main_applySpecFromProdJson_bc<F_O, F_N>(F_forward: F_O->F_N, F_backward: F_N->F_O, j_O: Old.difftest.helpers.Json, fn_O: string, j_N: New.difftest.helpers.Json, fn_N: string)
        decreases j_O, fn_O
        requires Old.difftest.helpers.deserializerAcceptsSubterms(Old.difftest.main.applySpecFromProdJson, j_O)
        requires j_N == Json_forward(j_O)
        requires fn_N == fn_O
        requires forall x_O: F_O :: F_backward(F_forward(x_O)) == x_O
        ensures New.difftest.helpers.deserializerAcceptsSubterms(New.difftest.main.applySpecFromProdJson, j_N)
        ensures New.difftest.helpers.deserializeField(j_N, fn_N, New.difftest.main.applySpecFromProdJson) == FromProdResult_forward((x: Joint.validation.validator.TypecheckerApplySpec) => x, (x: Joint.validation.validator.TypecheckerApplySpec) => x, Old.difftest.helpers.deserializeField(j_O, fn_O, Old.difftest.main.applySpecFromProdJson))
      {
        assert New.difftest.helpers.deserializeField(j_N, fn_N, New.difftest.main.applySpecFromProdJson) == FromProdResult_forward((x: Joint.validation.validator.TypecheckerApplySpec) => x, (x: Joint.validation.validator.TypecheckerApplySpec) => x, var jf :- (getJsonField_bc(j_O, fn_O, j_N, fn_N);
        Old.difftest.helpers.getJsonField(j_O, fn_O));
        Old.difftest.main.applySpecFromProdJson(jf));
      }

      lemma deserializeField_2_difftest_main_entityUIDEntryFromProdJson_bc<F_O, F_N>(F_forward: F_O->F_N, F_backward: F_N->F_O, j_O: Old.difftest.helpers.Json, fn_O: string, j_N: New.difftest.helpers.Json, fn_N: string)
        decreases j_O, fn_O
        requires Old.difftest.helpers.deserializerAcceptsSubterms(Old.difftest.main.entityUIDEntryFromProdJson, j_O)
        requires j_N == Json_forward(j_O)
        requires fn_N == fn_O
        requires forall x_O: F_O :: F_backward(F_forward(x_O)) == x_O
        ensures New.difftest.helpers.deserializerAcceptsSubterms(New.difftest.main.entityUIDEntryFromProdJson, j_N)
        ensures New.difftest.helpers.deserializeField(j_N, fn_N, New.difftest.main.entityUIDEntryFromProdJson) == FromProdResult_forward((x: Joint.def.core.EntityUID) => x, (x: Joint.def.core.EntityUID) => x, Old.difftest.helpers.deserializeField(j_O, fn_O, Old.difftest.main.entityUIDEntryFromProdJson))
      {
        assert New.difftest.helpers.deserializeField(j_N, fn_N, New.difftest.main.entityUIDEntryFromProdJson) == FromProdResult_forward((x: Joint.def.core.EntityUID) => x, (x: Joint.def.core.EntityUID) => x, var jf :- (getJsonField_bc(j_O, fn_O, j_N, fn_N);
        Old.difftest.helpers.getJsonField(j_O, fn_O));
        Old.difftest.main.entityUIDEntryFromProdJson(jf));
      }

      lemma {:axiom} deserializeTuple2Elts_bc<T_O, T_N, E1_O, E1_N, E2_O, E2_N>(T_forward: T_O->T_N, T_backward: T_N->T_O, E1_forward: E1_O->E1_N, E1_backward: E1_N->E1_O, E2_forward: E2_O->E2_N, E2_backward: E2_N->E2_O, j_O: Old.difftest.helpers.Json, ed1_O: Old.difftest.helpers.PartialDeserializer<E1_O>, ed2_O: Old.difftest.helpers.PartialDeserializer<E2_O>, cons_O: (E1_O,E2_O)->Old.difftest.helpers.FromProdResult<T_O>, j_N: New.difftest.helpers.Json, ed1_N: New.difftest.helpers.PartialDeserializer<E1_N>, ed2_N: New.difftest.helpers.PartialDeserializer<E2_N>, cons_N: (E1_N,E2_N)->New.difftest.helpers.FromProdResult<T_N>)
        decreases j_O
        requires Old.difftest.helpers.deserializerAcceptsSubterms(ed1_O, j_O) && Old.difftest.helpers.deserializerAcceptsSubterms(ed2_O, j_O)
        requires j_N == Json_forward(j_O)
        requires ed1_N == PartialDeserializer_forward(E1_forward, E1_backward, ed1_O)
        requires ed2_N == PartialDeserializer_forward(E2_forward, E2_backward, ed2_O)
        requires forall x1_N: E1_N, x2_N: E2_N :: cons_N(x1_N, x2_N) == FromProdResult_forward(T_forward, T_backward, cons_O(E1_backward(x1_N), E2_backward(x2_N)))
        requires forall x_O: T_O :: T_backward(T_forward(x_O)) == x_O
        requires forall x_O: E1_O :: E1_backward(E1_forward(x_O)) == x_O
        requires forall x_O: E2_O :: E2_backward(E2_forward(x_O)) == x_O
        ensures New.difftest.helpers.deserializerAcceptsSubterms(ed1_N, j_N) && New.difftest.helpers.deserializerAcceptsSubterms(ed2_N, j_N)
        ensures New.difftest.helpers.deserializeTuple2Elts(j_N, ed1_N, ed2_N, cons_N) == FromProdResult_forward(T_forward, T_backward, Old.difftest.helpers.deserializeTuple2Elts(j_O, ed1_O, ed2_O, cons_O))

      lemma {:axiom} deserializeTuple2Elts_1_difftest_main_entityUIDFromProdJson_bc<T_O, T_N, E1_O, E1_N, E2_O, E2_N>(T_forward: T_O->T_N, T_backward: T_N->T_O, E1_forward: E1_O->E1_N, E1_backward: E1_N->E1_O, E2_forward: E2_O->E2_N, E2_backward: E2_N->E2_O, j_O: Old.difftest.helpers.Json, ed2_O: Old.difftest.helpers.PartialDeserializer<E2_O>, cons_O: (Joint.def.core.EntityUID,E2_O)->Old.difftest.helpers.FromProdResult<Joint.def.core.EntityUID>, j_N: New.difftest.helpers.Json, ed2_N: New.difftest.helpers.PartialDeserializer<E2_N>, cons_N: (Joint.def.core.EntityUID,E2_N)->New.difftest.helpers.FromProdResult<Joint.def.core.EntityUID>)
        decreases j_O
        requires Old.difftest.helpers.deserializerAcceptsSubterms(Old.difftest.main.entityUIDFromProdJson, j_O) && Old.difftest.helpers.deserializerAcceptsSubterms(ed2_O, j_O)
        requires j_N == Json_forward(j_O)
        requires ed2_N == PartialDeserializer_forward(E2_forward, E2_backward, ed2_O)
        requires forall x1_N: Joint.def.core.EntityUID, x2_N: E2_N :: cons_N(x1_N, x2_N) == FromProdResult_forward((x: Joint.def.core.EntityUID) => x, (x: Joint.def.core.EntityUID) => x, cons_O(x1_N, E2_backward(x2_N)))
        requires forall x_O: T_O :: T_backward(T_forward(x_O)) == x_O
        requires forall x_O: E1_O :: E1_backward(E1_forward(x_O)) == x_O
        requires forall x_O: E2_O :: E2_backward(E2_forward(x_O)) == x_O
        ensures New.difftest.helpers.deserializerAcceptsSubterms(New.difftest.main.entityUIDFromProdJson, j_N) && New.difftest.helpers.deserializerAcceptsSubterms(ed2_N, j_N)
        ensures New.difftest.helpers.deserializeTuple2Elts(j_N, New.difftest.main.entityUIDFromProdJson, ed2_N, cons_N) == FromProdResult_forward((x: Joint.def.core.EntityUID) => x, (x: Joint.def.core.EntityUID) => x, Old.difftest.helpers.deserializeTuple2Elts(j_O, Old.difftest.main.entityUIDFromProdJson, ed2_O, cons_O))

      lemma {:axiom} setDeserializer_bc<T_O, T_N>(T_forward: T_O->T_N, T_backward: T_N->T_O, ed_O: Old.difftest.helpers.Deserializer<T_O>, ed_N: New.difftest.helpers.Deserializer<T_N>)
        requires ed_N == Deserializer_forward(T_forward, T_backward, ed_O)
        requires forall x_O: T_O :: T_backward(T_forward(x_O)) == x_O
        ensures New.difftest.helpers.setDeserializer(ed_N) == Deserializer_forward((x: set<T_O>) => Translations.MapBuiltinTypes.Set(T_forward, x), (x: set<T_N>) => Translations.MapBuiltinTypes.Set(T_backward, x), Old.difftest.helpers.setDeserializer(ed_O))

      lemma {:axiom} setDeserializer_0_difftest_main_entityUIDFromProdJson_bc<T_O, T_N>(T_forward: T_O->T_N, T_backward: T_N->T_O)
        requires forall x_O: T_O :: T_backward(T_forward(x_O)) == x_O
        ensures New.difftest.helpers.setDeserializer(New.difftest.main.entityUIDFromProdJson) == Deserializer_forward((x: set<Joint.def.core.EntityUID>) => x, (x: set<Joint.def.core.EntityUID>) => x, Old.difftest.helpers.setDeserializer(Old.difftest.main.entityUIDFromProdJson))

      lemma setDeserializer_0_difftest_main_entitytypeFromProdJsonOption_bc<T_O, T_N>(T_forward: T_O->T_N, T_backward: T_N->T_O)
        requires forall x_O: T_O :: T_backward(T_forward(x_O)) == x_O
        ensures New.difftest.helpers.setDeserializer(New.difftest.main.entitytypeFromProdJsonOption) == Deserializer_forward((x: set<Joint.def.std.Option<Joint.def.core.EntityType>>) => x, (x: set<Joint.def.std.Option<Joint.def.core.EntityType>>) => x, Old.difftest.helpers.setDeserializer(Old.difftest.main.entitytypeFromProdJsonOption))
      {
        forall j: Old.difftest.helpers.Json
          ensures New.difftest.helpers.setDeserializer(New.difftest.main.entitytypeFromProdJsonOption)(Json_forward(j)) == FromProdResult_forward((x: set<Joint.def.std.Option<Joint.def.core.EntityType>>) => x, (x: set<Joint.def.std.Option<Joint.def.core.EntityType>>) => x, Old.difftest.helpers.setDeserializer(Old.difftest.main.entitytypeFromProdJsonOption)(j)) {
          assert New.difftest.helpers.setDeserializer(New.difftest.main.entitytypeFromProdJsonOption)(Json_forward(j)) == FromProdResult_forward((x: set<Joint.def.std.Option<Joint.def.core.EntityType>>) => x, (x: set<Joint.def.std.Option<Joint.def.core.EntityType>>) => x, Old.difftest.helpers.setDeserializer(Old.difftest.main.entitytypeFromProdJsonOption)(j));
        }
      }

      lemma {:axiom} sumDeserializer_bc<T_O, T_N>(T_forward: T_O->T_N, T_backward: T_N->T_O, consMap_O: map<string,Old.difftest.helpers.Deserializer<T_O>>, consMap_N: map<string,New.difftest.helpers.Deserializer<T_N>>)
        decreases consMap_O
        requires consMap_N == Translations.MapBuiltinTypes.Map((mp: string) => mp, (mp: string) => mp, (mp: Old.difftest.helpers.Deserializer<T_O>) => Deserializer_forward(T_forward, T_backward, mp), consMap_O)
        requires forall x_O: T_O :: T_backward(T_forward(x_O)) == x_O
        ensures New.difftest.helpers.sumDeserializer(consMap_N) == Deserializer_forward(T_forward, T_backward, Old.difftest.helpers.sumDeserializer(consMap_O))

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

      lemma entitytypeFromProdJson_bc()
        ensures Deserializer_forward((x: Joint.def.core.EntityType) => x, (x: Joint.def.core.EntityType) => x, Old.difftest.main.entitytypeFromProdJson) == New.difftest.main.entitytypeFromProdJson
      {}

      lemma {:axiom} entityUIDFromProdJson_bc()
        ensures Deserializer_forward((x: Joint.def.core.EntityUID) => x, (x: Joint.def.core.EntityUID) => x, Old.difftest.main.entityUIDFromProdJson) == New.difftest.main.entityUIDFromProdJson

      lemma entityUIDEntryFromProdJson_bc()
        ensures Deserializer_forward((x: Joint.def.core.EntityUID) => x, (x: Joint.def.core.EntityUID) => x, Old.difftest.main.entityUIDEntryFromProdJson) == New.difftest.main.entityUIDEntryFromProdJson
      {}

      lemma getEntityUIDEntryField_bc(request_O: Old.difftest.helpers.Json, f_O: string, request_N: New.difftest.helpers.Json, f_N: string)
        decreases request_O, f_O
        requires request_N == Json_forward(request_O)
        requires f_N == f_O
        ensures New.difftest.main.getEntityUIDEntryField(request_N, f_N) == FromProdResult_forward((x: Joint.def.core.EntityUID) => x, (x: Joint.def.core.EntityUID) => x, Old.difftest.main.getEntityUIDEntryField(request_O, f_O))
      {
        deserializeField_2_difftest_main_entityUIDEntryFromProdJson_bc((x: Joint.def.core.EntityUID) => x, (x: Joint.def.core.EntityUID) => x, request_O, f_O, request_N, f_N);
        assert New.difftest.main.getEntityUIDEntryField(request_N, f_N) == FromProdResult_forward((x: Joint.def.core.EntityUID) => x, (x: Joint.def.core.EntityUID) => x, Old.difftest.helpers.deserializeField(request_O, f_O, Old.difftest.main.entityUIDEntryFromProdJson));
      }

      lemma {:axiom} attrTypesFromProdJsonObject_bc(j_O: Old.difftest.helpers.Json, j_N: New.difftest.helpers.Json)
        decreases j_O
        requires j_N == Json_forward(j_O)
        ensures New.difftest.main.attrTypesFromProdJsonObject(j_N) == FromProdResult_forward((x: map<Joint.def.core.Attr,Joint.validation.types.AttrType>) => x, (x: map<Joint.def.core.Attr,Joint.validation.types.AttrType>) => x, Old.difftest.main.attrTypesFromProdJsonObject(j_O))

      lemma entitytypeFromProdJsonOption_bc()
        ensures Deserializer_forward((x: Joint.def.std.Option<Joint.def.core.EntityType>) => x, (x: Joint.def.std.Option<Joint.def.core.EntityType>) => x, Old.difftest.main.entitytypeFromProdJsonOption) == New.difftest.main.entitytypeFromProdJsonOption
      {}

      lemma applySpecFromProdJson_bc(j_O: Old.difftest.helpers.Json, j_N: New.difftest.helpers.Json)
        decreases j_O
        requires j_N == Json_forward(j_O)
        ensures New.difftest.main.applySpecFromProdJson(j_N) == FromProdResult_forward((x: Joint.validation.validator.TypecheckerApplySpec) => x, (x: Joint.validation.validator.TypecheckerApplySpec) => x, Old.difftest.main.applySpecFromProdJson(j_O))
      {
        assert New.difftest.main.applySpecFromProdJson(j_N) == FromProdResult_forward((x: Joint.validation.validator.TypecheckerApplySpec) => x, (x: Joint.validation.validator.TypecheckerApplySpec) => x, var pas :- (deserializeField_bc((x: set<Joint.def.std.Option<Joint.def.core.EntityType>>) => x, (x: set<Joint.def.std.Option<Joint.def.core.EntityType>>) => x, j_O, "principalApplySpec", Old.difftest.helpers.setDeserializer(Old.difftest.main.entitytypeFromProdJsonOption), j_N, "principalApplySpec", New.difftest.helpers.setDeserializer(New.difftest.main.entitytypeFromProdJsonOption));
        Old.difftest.helpers.deserializeField(j_O, "principalApplySpec", setDeserializer_0_difftest_main_entitytypeFromProdJsonOption_bc((x: Joint.def.std.Option<Joint.def.core.EntityType>) => x, (x: Joint.def.std.Option<Joint.def.core.EntityType>) => x);
        Old.difftest.helpers.setDeserializer(Old.difftest.main.entitytypeFromProdJsonOption)));
        var ras :- (deserializeField_bc((x: set<Joint.def.std.Option<Joint.def.core.EntityType>>) => x, (x: set<Joint.def.std.Option<Joint.def.core.EntityType>>) => x, j_O, "resourceApplySpec", Old.difftest.helpers.setDeserializer(Old.difftest.main.entitytypeFromProdJsonOption), j_N, "resourceApplySpec", New.difftest.helpers.setDeserializer(New.difftest.main.entitytypeFromProdJsonOption));
        Old.difftest.helpers.deserializeField(j_O, "resourceApplySpec", setDeserializer_0_difftest_main_entitytypeFromProdJsonOption_bc((x: Joint.def.std.Option<Joint.def.core.EntityType>) => x, (x: Joint.def.std.Option<Joint.def.core.EntityType>) => x);
        Old.difftest.helpers.setDeserializer(Old.difftest.main.entitytypeFromProdJsonOption)));
        Joint.def.std.Result.Ok(Joint.validation.validator.TypecheckerApplySpec.TypecheckerApplySpec(pas, ras)));
      }

      lemma actionIdPairFromProdJson_bc(j_O: Old.difftest.helpers.Json, j_N: New.difftest.helpers.Json)
        decreases j_O
        requires j_N == Json_forward(j_O)
        ensures New.difftest.main.actionIdPairFromProdJson(j_N) == FromProdResult_forward((x: (Joint.def.core.EntityUID,Joint.validation.validator.TypecheckerActionId)) => (x.0, x.1), (x: (Joint.def.core.EntityUID,Joint.validation.validator.TypecheckerActionId)) => (x.0, x.1), Old.difftest.main.actionIdPairFromProdJson(j_O))
      {
        deserializeTuple2Elts_1_difftest_main_entityUIDFromProdJson_bc((x: (Joint.def.core.EntityUID,Joint.validation.validator.TypecheckerActionId)) => (x.0, x.1), (x: (Joint.def.core.EntityUID,Joint.validation.validator.TypecheckerActionId)) => (x.0, x.1), (x: Joint.def.core.EntityUID) => x, (x: Joint.def.core.EntityUID) => x, (x: Joint.validation.validator.TypecheckerActionId) => x, (x: Joint.validation.validator.TypecheckerActionId) => x, j_O, (data: Old.difftest.helpers.Json) => var appliesTo :- Old.difftest.helpers.deserializeField(data, "appliesTo", Old.difftest.main.applySpecFromProdJson);
        var descendants :- Old.difftest.helpers.deserializeField(data, "descendants", Old.difftest.helpers.setDeserializer(Old.difftest.main.entityUIDFromProdJson));
        var context :- Old.difftest.helpers.getJsonField(data, "context");
        var context1 :- Old.difftest.helpers.deserializeField(context, "attrs", Old.difftest.main.attrTypesFromProdJsonObject);
        Joint.def.std.Result.Ok(Joint.validation.validator.TypecheckerActionId.TypecheckerActionId(appliesTo, descendants, context1)), (uid: Joint.def.core.EntityUID, act: Joint.validation.validator.TypecheckerActionId) => Joint.def.std.Result.Ok(uid), j_N, (data: New.difftest.helpers.Json) => var appliesTo :- New.difftest.helpers.deserializeField(data, "appliesTo", New.difftest.main.applySpecFromProdJson);
        var descendants :- New.difftest.helpers.deserializeField(data, "descendants", New.difftest.helpers.setDeserializer(New.difftest.main.entityUIDFromProdJson));
        var context :- New.difftest.helpers.getJsonField(data, "context");
        var context1 :- New.difftest.helpers.deserializeField(context, "attrs", New.difftest.main.attrTypesFromProdJsonObject);
        Joint.def.std.Result.Ok(Joint.validation.validator.TypecheckerActionId.TypecheckerActionId(appliesTo, descendants, context1)), (uid: Joint.def.core.EntityUID, act: Joint.validation.validator.TypecheckerActionId) => Joint.def.std.Result.Ok(uid));
        assert New.difftest.main.actionIdPairFromProdJson(j_N) == FromProdResult_forward((x: (Joint.def.core.EntityUID,Joint.validation.validator.TypecheckerActionId)) => (x.0, x.1), (x: (Joint.def.core.EntityUID,Joint.validation.validator.TypecheckerActionId)) => (x.0, x.1), Old.difftest.helpers.deserializeTuple2Elts(j_O, Old.difftest.main.entityUIDFromProdJson, (data: Old.difftest.helpers.Json) => var appliesTo :- (deserializeField_2_difftest_main_applySpecFromProdJson_bc((x: Joint.validation.validator.TypecheckerApplySpec) => x, (x: Joint.validation.validator.TypecheckerApplySpec) => x, data, "appliesTo", Json_forward(data), "appliesTo");
        Old.difftest.helpers.deserializeField(data, "appliesTo", Old.difftest.main.applySpecFromProdJson));
        var descendants :- (deserializeField_bc((x: set<Joint.def.core.EntityUID>) => x, (x: set<Joint.def.core.EntityUID>) => x, data, "descendants", Old.difftest.helpers.setDeserializer(Old.difftest.main.entityUIDFromProdJson), Json_forward(data), "descendants", New.difftest.helpers.setDeserializer(New.difftest.main.entityUIDFromProdJson));
        Old.difftest.helpers.deserializeField(data, "descendants", setDeserializer_0_difftest_main_entityUIDFromProdJson_bc((x: Joint.def.core.EntityUID) => x, (x: Joint.def.core.EntityUID) => x);
        Old.difftest.helpers.setDeserializer(Old.difftest.main.entityUIDFromProdJson)));
        var context :- (getJsonField_bc(data, "context", Json_forward(data), "context");
        Old.difftest.helpers.getJsonField(data, "context"));
        var context1 :- (deserializeField_2_difftest_main_attrTypesFromProdJsonObject_bc((x: map<Joint.def.core.Attr,Joint.validation.types.AttrType>) => x, (x: map<Joint.def.core.Attr,Joint.validation.types.AttrType>) => x, context, "attrs", Json_forward(context), "attrs");
        Old.difftest.helpers.deserializeField(context, "attrs", Old.difftest.main.attrTypesFromProdJsonObject));
        Joint.def.std.Result.Ok(Joint.validation.validator.TypecheckerActionId.TypecheckerActionId(appliesTo, descendants, context1)), (uid: Joint.def.core.EntityUID, act: Joint.validation.validator.TypecheckerActionId) => Joint.def.std.Result.Ok((uid, act))));
      }

      import opened def.base

      import opened def.core

      import opened def.engine

      import opened def.std

      import opened def.templates

      import opened def.ext.fun

      import opened def.util

      import opened restrictedExpr

      import opened validation.types

      import opened validation.typechecker

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
