namespace TypeInjections

open YIL

module Analysis =
  /// dependency of two declarations
  /// DepSpec: used in specification but not body
  /// DepComp: used in specification and/or body
  type Dependency =
      | DepNone | DepSpec | DepComp
      /// DepNone < DepSpec < DepComp
      member this.union(that: Dependency) =
          match this,that with
          | DepComp,_ | _,DepComp -> DepComp
          | DepSpec,_ | _,DepSpec -> DepSpec
          | _ -> DepNone

  /// helper class of usedBy
  type UsedByTraverser(p: Path) =
      inherit Traverser.Identity()
      let mutable dep = DepNone
      member this.getDep() = dep
      override this.path(ctx: Context, q:Path) =
          if p.isAncestorOf(q) then
             let d = if ctx.pos = BodyPosition then DepComp else DepSpec
             dep <- dep.union(d)
          q
  /// returns info on if/how p is used in d
  let usedBy(ctx: Context, p: Path, d: Decl): Dependency =
      let c = UsedByTraverser(p)
      c.decl(ctx, d) |> ignore
      c.getDep()
  
  /// for a list 'ds' of declarations making up the body of the current declaration,
  /// return the dependency closure of a subset 'start' of those declarations (reflexive, transitive) 
  let dependencyClosure(ctx: Context, ds: Decl list, start: Path list) =
      let mutable closure: Path list = []
      let rec add(p: Path) =
         closure <- p :: closure
         // recurse for every declaration not already in the closure and used by p
         List.iter (fun (d:Decl) ->
             let dp = ctx.currentDecl.child(d.name)
             if not (List.contains dp closure) && usedBy(ctx, p, d) <> DepNone then
                add(dp)
             ) ds
      List.iter add start
      closure