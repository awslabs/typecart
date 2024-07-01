// a simple term language with strings and propositions that is evaluated against a context holding variable definitions 

module CommonTypes {
   datatype Context = | Context(vars: seq<(string, string)>)

   datatype Term = | Var(n: string) | Concat(l: Term, r: Term)
   datatype Prop = | And(l: Prop, r: Prop) | Not(p: Prop) | Equal(tl: Term, tr: Term)

   datatype Option<+U> = | None() | Some(val: U)
}

module ContextEval {
   import opened CommonTypes
   function Eval(ctx: Context, condition: Prop) : bool {
      match condition {
         case And(l, r) => Eval(ctx, l) && Eval(ctx, r)
         case Not(p) => !Eval(ctx, p)
         case Equal(tl, tr) => EvalTerm(ctx, tl) == EvalTerm(ctx, tr)
      }
   }

   function EvalTerm(ctx: Context, t: Term): Option<string> {
      match t {
         case Var(n) => Lookup(ctx, n)
         case Concat(l, r) =>
            var lval := EvalTerm(ctx, l);
            var rval := EvalTerm(ctx, r);
            if lval.None? || rval.None? then
               None()
            else
               Some(lval.val + rval.val)
      }
   }

   function Lookup(ctx: Context, k: string): Option<string> {
      Find(ctx.vars, k)
   }

   function RemoveSpace(v: string): string {
      if v == "" then
         ""
      else if v[0] == ' ' then
         RemoveSpace(v[1..])
      else
         [v[0]] + RemoveSpace(v[1..])
   }

   function Find(vars: seq<(string, string)>, k: string): Option<string> {
      if vars == [] then
         None()
      else if vars[0].0 == k then
         if ' ' !in vars[0].1 then
            Some(vars[0].1)
         else
            Some(RemoveSpace(vars[0].1))
      else
         Find(vars[1..], k)
   }
}
