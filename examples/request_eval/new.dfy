// a simple language of statements that are evaluated against contexts

module CommonTypes {
   datatype Option<+U> = | None() | Some(val: U)
}

module Types {
   // contexts are lists of key-value pairs
   datatype Context = | Context(entries: seq<Entry>)
   datatype Entry = | Entry(key: string, value: string)

   // a statement is a conjunction of atoms   
   datatype Statement = | Statement(atoms: seq<Atom>)
   // an atom consists of an operator that is applied to (the context value corresponding to) a key and a list values
   datatype Atom = | Atom(operation: Operation, key: string, values: seq<string>)
   // OneOf tests if the first context value with that key exists and is among the provided list of values
   // AllOf tests if all context values with that key are among the provided list of values
   // Exists tests if any context entry with that key exists
   datatype Operation = | OneOf | AllOf | Exists
}

module Evaluation {
   import opened CommonTypes
   import opened Types

   function EvalStatement(ctx: Context, s: Statement): bool {
      forall a:: a in s.atoms ==> EvalAtom(ctx, a)
   }

   function EvalAtom(ctx: Context, a: Atom): bool {
      match a.operation {
         case OneOf => EvalOneOf(ctx, a)
         case AllOf => EvalAllOf(ctx, a)
         case Exists => EvalExists(ctx, a.key)
      }
   }

   function EvalOneOf(ctx: Context, a: Atom): bool {
      match Lookup(ctx.entries, a.key) {
         case None() => false
         case Some(v) => v in a.values
      }
   }

   function EvalAllOf(ctx: Context, a: Atom): bool {
      forall v:: v in LookupAll(ctx.entries, a.key) ==> v in a.values
   }

   function EvalExists(ctx: Context, k: string): bool {
      exists e:: e in ctx.entries && e.key == k
   }

   function Lookup(entries: seq<Entry>, k: string): Option<string> {
      if entries == [] then None()
      else
         var e := entries[0];
         if e.key == k then Some(e.value)
         else Lookup(entries[1..], k)
   }

   function LookupAll(entries: seq<Entry>, k: string): seq<string> {
      if entries == [] then []
      else
         var e := entries[0];
         if e.key == k then [e.value] + LookupAll(entries[1..], k)
         else LookupAll(entries[1..], k)
   }
}
