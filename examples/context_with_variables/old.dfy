// a simple term language with strings and propositions that is evaluated against a context holding variable definitions 

datatype Context = | Context(vars: seq<(string, string)>)

datatype Predicate = | Equal | Contains | Present
 
datatype Prop = | And(l: Prop, r: Prop) | Not(p: Prop) | Equal(l: string, r: string)
datatype Term = | Var(n: string) | Concat(l: string, r: string)


function Eval(ctx: Context, condition: Prop) : bool {
   match condition {
     case And(l,r) => Eval(ctx, l) && Eval(ctx, r)
     case Not(p) => !Eval(ctx, p)
     case Equal(l,r) => EvalTerm(ctx, r) == EvalTerm(Ctx,l)
   }
}

function EvalTerm(ctx: Context, t: Term): string {
   match t {
    case Var(n) => Lookup(ctx,n)
    case Concat(l,r) => EvalTerm(ctx,l) + EvalTerm(ctx,r)
   }
}

// need to add option type
function Lookup(ctx: Context, v: string): Option<bool> {
   ctx.find((k,y) => k == v) // pseudo code 
}

// new version: if a variable name contains a $, something different happens
function NewLookup(ctx: Context, v: string): Option<bool> {
   var v := ctx.find((k,y) => k == v) // pseudo code 
   if (k does not contain "$") v else {need to find something reasonable to do here}
}
