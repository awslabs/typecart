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
        match R_O {
          case Ok(b) =>
            Joint.validation.types.Ok(T_forward(b))
          case Err(e) =>
            Joint.validation.types.Err(e)
        }
      }

      function Result_backward<T_O, T_N>(T_forward: T_O->T_N, T_backward: T_N->T_O, R_N: Joint.validation.types.Result<T_N>): Joint.validation.types.Result<T_O>
      {
        match R_N {
          case Ok(b) =>
            Joint.validation.types.Ok(T_backward(b))
          case Err(e) =>
            Joint.validation.types.Err(e)
        }
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

      lemma {:axiom} entityUIDFromProdJson_bc()
        ensures Deserializer_forward((x: Joint.def.core.EntityUID) => x, (x: Joint.def.core.EntityUID) => x, Old.difftest.main.entityUIDFromProdJson) == New.difftest.main.entityUIDFromProdJson

      lemma getEntityUIDEntryField_bc(request_O: Old.difftest.helpers.Json, f_O: string, request_N: New.difftest.helpers.Json, f_N: string)
        decreases request_O, f_O
        requires request_N == Json_forward(request_O)
        requires f_N == f_O
        ensures New.difftest.main.getEntityUIDEntryField(request_N, f_N) == FromProdResult_forward((x: Joint.def.core.EntityUID) => x, (x: Joint.def.core.EntityUID) => x, Old.difftest.main.getEntityUIDEntryField(request_O, f_O))
      {
        assert New.difftest.main.getEntityUIDEntryField(request_N, f_N) == FromProdResult_forward((x: Joint.def.core.EntityUID) => x, (x: Joint.def.core.EntityUID) => x, var json :- (getJsonField_bc(request_O, f_O, request_N, f_N);
        Old.difftest.helpers.getJsonField(request_O, f_O));
        var known :- (getJsonField_bc(json, "Known", Json_forward(json), "Known");
        Old.difftest.helpers.getJsonField(json, "Known"));
        var euid :- (getJsonField_bc(known, "euid", Json_forward(known), "euid");
        Old.difftest.helpers.getJsonField(known, "euid"));
        Old.difftest.main.entityUIDFromProdJson(euid));
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
        match R_O {
          case Ok(b) =>
            Joint.def.base.Ok(T_forward(b))
          case Err(e) =>
            Joint.def.base.Err(e)
        }
      }

      function Result_backward<T_O, T_N>(T_forward: T_O->T_N, T_backward: T_N->T_O, R_N: Joint.def.base.Result<T_N>): Joint.def.base.Result<T_O>
      {
        match R_N {
          case Ok(b) =>
            Joint.def.base.Ok(T_backward(b))
          case Err(e) =>
            Joint.def.base.Err(e)
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
