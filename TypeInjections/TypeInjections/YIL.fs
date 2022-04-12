namespace TypeInjections

// DotNet, for number literals
open System
open System.Numerics
open Microsoft.BaseTypes

// Yucca
open UtilsFR

(* AST for the relevant fragment of Dafny
   adapted from the YuccaIntermediateLanguage of YuccaDafnyCompiler, commit 15bd2b1d9a45fb1799afacd60439454e56f431cd
*)

// TODO the ghost attribute is more complex than was assumed here, which may have caused a bug

module YIL =
    let error msg = failwith msg

    /// a qualified identifier of a declaration, see lookupByPath for semantics
    type Path =
        | Path of string list
        member this.names =
            match this with
            | Path (ns) -> ns

        member this.isRoot = this.names.IsEmpty

        member this.child(n: string) =
            if n = "" then
                this
            else
                Path(this.names @ [ n ])

        member this.append(ns: Path) =
            Path(
                this.names
                @ List.filter (fun x -> x <> "") ns.names
            )

        member this.parent = Path(listDropLast (this.names))
        member this.name = listLast (this.names)

        member this.isAncestorOf(p: Path) =
            let l = this.names.Length

            p.names.Length >= l
            && p.names.[..l - 1] = this.names

        override this.ToString() = listToString (this.names, ".")

    (* toplevel declaration
       The program name corresponds to the package name or root namespace.

       This could be a special case of Decl or even just a Module.
       But for now we keep it separate because:
       - Modules aren't nested for now, and we want to forbid that altogether.
       - We way want to add information here later.
       - It is convenient to have a type of programs and not just a constructor.
    *)
    type Program = { name: string; decls: Decl list }

    (* declarations
       Modules and datatypes are child-bearing, i.e., can contain nested declarations.
       Each declaration is named uniquely within its parent.
       Within the program each declaration is uniquely identified.
    *)
    and Decl =
        (* We do not allow module abstraction, inheritance; modules are just namespaces and are not used as types.
           In other words, children of a module are static and globally visible via their qualified identifier.

           Internally, Dafny wraps all fields/methods of a module in a default class.
           We do not mimic that here.
           Also, all declarations outside a module are wrapped in a default module. We do not allow those.
        *)
        | Module of name: string * decls: Decl list * meta: Meta
        (* Datatypes subsume inductive types (= special case where there are no members) and
           classes (= special case where there is only one constructor).
           Like with inductive types and unlike with classes, two different constructors always produce different objects.
           Members cannot be private, abstract, or mutable.
           If multiple constructors have arguments of the same name, they must have the same type.
        *)
        | Datatype of
            name: string *
            tpvars: string list *
            constructors: DatatypeConstructor list *
            members: Decl list *
            meta: Meta
        (* Class declarations in Dafny *)
        | Class of
            name: string *
            isTrait: bool *
            tpvars: TypeArg list *
            parent: ClassType list *
            members: Decl list *
            meta: Meta
        (* Class constructor as opposed to the default constructor in Datatype *)
        | ClassConstructor of name: string * tpvars: string list * ins: LocalDecl list * body: Expr option * meta: Meta
        (* Type definitions
           if predicate is given: HOL-style subtype definitions (omitting the witness here)
             else: type synonym
           if isNew: type is not a subtype of the supertype (which must be nat or real and thus tpvars = [])
        *)
        | TypeDef of
            name: string *
            tpvars: TypeArg list *
            super: Type *
            predicate: (string * Expr) option *
            isNew: bool *
            meta: Meta
        (* Dafny declares mutable fields only in classes, and then without initializer deferring initialization to the class constructor.
           Immutable fields are called ConstantField in Dafny.
        *)
        | Field of
            name: string *
            tp: Type *
            init: Expr option *
            ghost: bool *
            isStatic: bool *
            isMutable: bool *
            meta: Meta
        (* methods *)
        | Method of
            isLemma: bool *
            name: string *
            tpvars: TypeArg list *
            ins: InputSpec *
            out: OutputSpec *
            body: Expr option *
            ghost: bool *
            isStatic: bool *
            meta: Meta
        | Export of Path list
        // dummy for missing cases
        | DUnimplemented
        member this.meta =
            match this with
            | Module (_, _, meta) -> meta
            | Datatype (_, _, _, _, meta) -> meta
            | Class (_, _, _, _, _, meta) -> meta
            | Method (_,_, _, _, _, _, _, _, meta) -> meta
            | Field (_, _, _, _, _, _, meta) -> meta
            | TypeDef (_, _, _, _, _, meta) -> meta
            | _ -> { position = None }

        member this.name =
            match this with
            | Module (n, _, _) -> n
            | Datatype (n, _, _, _, _) -> n
            | Class (n, _, _, _, _, _) -> n
            | ClassConstructor (n, _, _, _, _) -> n
            | Method (_,n, _, _, _, _, _, _, _) -> n
            | Field (n, _, _, _, _, _, _) -> n
            | TypeDef (n, _, _, _, _, _) -> n
            | Export _
            | DUnimplemented -> "" // check if this causes problems
        // type arguments of a declaration
        member this.tpvars =
            match this with
            | Module _ -> []
            | Datatype (_, tpvs, _, _, _) -> tpvs
            | Class (_, _, tpvs, _, _, _) -> tpvs
            | TypeDef (_, tpvs, _, _, _, _) -> tpvs
            | Field _ -> []
            | Method (_,_, tpvs, _, _, _, _, _, _) -> tpvs
            | ClassConstructor (_, tpvs, _, _, _) -> tpvs
            | Export _ -> error "export does not have type arguments"
            | DUnimplemented -> error "skipped declaration has no name"

    and TypeArg = string
    
    (* types
       We do not allow module inheritance or Dafny classes.
       Therefore, there is no subtyping except for numbers.
    *)
    and Type =
        // built-in base types
        | TUnit
        | TBool
        | TChar
        | TString
        | TNat
        | TInt
        | TReal
        | TBitVector of int
        // built-in type operators
        | TTuple of Type list
        | TFun of Type list * Type
        | TSeq of Type
        | TSet of Type
        | TMap of Type * Type
        | TArray of Type // array of any dimensions
        | TObject // supertype of all classes
        // identifiers
        | TApply of op: Path * args: Type list
        | TVar of string
        // dummy for missing cases
        | TUnimplemented
        override this.ToString() =
            let tps (ts: Type list) =
                if ts.IsEmpty then
                    ""
                else
                    "[" + listToString (ts, ",") + "]"

            match this with
            | TUnit -> "unit"
            | TBool -> "bool"
            | TInt -> "int"
            | TNat -> "nat"
            | TChar -> "char"
            | TString -> "string"
            | TReal -> "real"
            | TBitVector (w) -> "bv" + w.ToString()
            | TVar (n) -> n
            | TApply (op, args) -> op.name + (tps args)
            | TTuple (ts) -> tps ts
            | TFun (ins, out) -> (tps ins) + "=>" + (out.ToString())
            | TSeq (t) -> "seq" + (tps [ t ])
            | TSet (t) -> "set" + (tps [ t ])
            | TMap (d, r) -> "map" + (tps [ d; r ])
            | TArray (a) -> a.ToString() + "[]"
            | TObject -> "object"
            | TUnimplemented -> "UNIMPLEMENTED"

    (* typed variable declaration used in method input/output, binders, and local variables declararations
       All of those can be ghosts, i.e., only needed for specifications and proofs.
       Those can be removed when compiling for computation.
    *)
    and LocalDecl =
        LocalDecl of string * Type * bool
          member this.name = match this with | LocalDecl(n,_,_) -> n
          member this.tp = match this with | LocalDecl(_,t,_) -> t
          member this.ghost = match this with | LocalDecl(_,_,g) -> g
         
    
    (* pre/postcondition of a method/lemma *)
    and Condition = Expr

    (* constructor of an inductive type
    *)
    and DatatypeConstructor =
        { name: string
          ins: LocalDecl list
          meta: Meta }
    (* pattern match case
       Dafny's concrete syntax allows for nested constructors in patterns and literal patterns.
       But these are resolved away, and abstract syntax only shows pattern = c(x1,...,xn) where c is a
       constructor of the datatype being matched on and the x1 are the local decls.
       But we might generate more general constructors.
     *)
    and Case =
        { vars: LocalDecl list
          pattern: Expr
          body: Expr }

    and InputSpec = InputSpec of LocalDecl list * Condition list
    
    and OutputSpec =
        // usual case: return type
        | OutputType of Type * Condition list
        // case with multiple named outputs; empty list never seems to occur in Dafny
        | OutputDecls of LocalDecl list * Condition list
        member this.conditions =
            match this with
            | OutputType(_,cs) | OutputDecls(_,cs) -> cs

    (* a reference to a module or class with all its type parameters instantiated
       Since we do not use classes, this barely comes up, but
       it is how static methods in a module and the class of a new-operator are referenced.
    *)
    and ClassType = { path: Path; tpargs: Type list }

    (* expressions (uniquely typed)
       Dafny distinguishes expressions and statements; merged for now, but may have to be changed later.
    *)
    and Expr =
        // *** identifiers
        // reference to a field/method of an object of some child-bearing declaration
        // In some cases, we translate Dafny class fields to a combination of private fields and getter methods.
        // If a field comes with a getter method, we set `hasGetter` to true, and later translate accesses to getter
        // calls.
        | EMemberRef of receiver: Receiver * mmbr: Path * tpargs: Type list
        | EVar of name: string
        | EThis
        | ENew of tp: ClassType * args: Expr list
        | ENull of tp: Type
        | EArray of tp: Type * dim: Expr list // fixed size uninitialized array
        // built-in values of base types (literals)
        // Dafny represents nat literals as TInt literals even if the context demands it have type TNat.
        | EBool of bool
        // Dafny represents char and string literals as strings that include the escape characters as separate characters.
        | EChar of string
        | EString of string
        | EToString of expr: Expr list
        | EInt of BigInteger * tp: Type
        | EReal of BigDec * tp: Type
        // Dafny allows quantifiers in computations if the domain is finite; cond is a prediate that restricts the domain of the bound variables
        | EQuant of quant: Quantifier * ld: LocalDecl list * cond: Expr option * body: Expr
        | ETuple of elems: Expr list
        | EProj of tuple: Expr * index: int
        | EFun of vars: LocalDecl list * out: Type * body: Expr
        // *** introduction/elimination forms for built-in type operators
        | ESet of tp: Type * elems: Expr list
        | ESeq of tp: Type * elems: Expr list
        | EMapAt of mp: Expr * arg: Expr
        | EMapKeys of map: Expr
        | ESeqAt of seq: Expr * index: Expr
        | ESeqRange of seq: Expr * beginIndex: Expr option * endIndex: Expr option
        | ESeqUpdate of seq: Expr * index: Expr * df: Expr
        | EArrayAt of array: Expr * index: Expr list
        | EArrayUpdate of array: Expr * index: Expr list * value: Expr // in-place array update
        | ECharAt of str: Expr * index: Expr
        | EStringRange of str: Expr * beginIndex: Expr option * endIndex: Expr option
        // *** various forms of function applications
        // built-in unary and binary operators
        | EUnOpApply of op: string * arg: Expr
        | EBinOpApply of op: string * arg1: Expr * arg2: Expr
        // invocation of a method
        // if ghost is true, this is a ghost method like a lemma call
        // tpargs contains first type arguments of the enclosing datatype, then additional ones of the method
        | EMethodApply of receiver: Receiver * method: Path * tpargs: Type list * args: Expr list * ghost: bool
        // anonymous functions; maybe we want to forbid these eventually
        | EAnonApply of fn: Expr * args: Expr list
        // datatype constructors
        | EConstructorApply of cons: Path * tpargs: Type list * args: Expr list
        // type conversion
        | ETypeConversion of expr: Expr * toType: Type
        // *** control flow etc.
        | EBlock of exprs: Expr list
        | ELet of var: string * tp: Type * df: Expr * body: Expr
        | EIf of cond: Expr * thn: Expr * els: Expr option // cond must not have side-effects; els non-optional if this is an expression; see also flattenIf
        | EWhile of cond: Expr * body: Expr * label: (string option)
        | EFor of index: LocalDecl * init: Expr * last: Expr * up: bool * body: Expr
        | EReturn of Expr list // if empty, there is no return value or they have been set by assignments to the output variables
        | EBreak of string option
        | EMatch of on: Expr * tp: Type * cases: Case list * dflt: Expr option // Dafny never produces default cases, but we might
        (* *** declaration of a local mutable variable with optional initial value
           Multiple declarations appear at once because Dafny allows
            var x1,...,xn := V1,...,Vn  and  var x1,...,xn = V (if V is call to a method with n outputs).
           In the former case, x1 may not occur in V2.
           The latter is at most needed before ghosts are eliminated because we allow only one non-ghost output.
           Dafny also allows patterns on the lhs, but we do not allow that.
        *)
        | EDecls of (LocalDecl * UpdateRHS option) list
        (* assignment to mutable variables
           x1,...,xn := V
           Like for declarations, there may be multiple variables on the lhs.
           Because we only allow a single rhs, that only makes sense if the rhs is a method call.
           Dafny allows an omitted lhs, in which case this is just an expression;
           in particular, lemma calls are represented that way; because we merge statements and expressions,
           we do not need a special case for that.
        *)
        | EUpdate of name: Expr list * UpdateRHS
        (* variable declaration with non-deterministic initial value
           var x :| p(x)  for p:A->bool and resulting in x:A
           We do not need that, but it occasionally occurs in specifications.
        *)
        | EDeclChoice of LocalDecl * pred: Expr
        | EPrint of exprs: Expr list
        // temporary dummy for missing cases
        | EUnimplemented
    
    (* Dafny methods may return multiple outputs, and these may be named.
       This may seem awkward but is practical for specifications and proofs.
       We allow only the first output to be non-ghost.
     *)
    (* updates to variables may be plain (x:=V where x:A and V:A) or monadic (x:-V where V:M<A> and x:A)

       The latter is a binding to a variable of a value of monadic type.
       Dafny resolves x:-V based on 3 magic user-defined methods of datatype M into 3 statements:
          valueOrError : M<A> = V
          if valueOrError.isFailure() then return valueOrError.PropagateFailure()
          x : A = valueOrError.Extract()

       This syntax is allowed both in declarations (var x:-V) and assignments (var x:A; ...; x:-V).
       This type represents the commonalities of the two cases:
       - monadic = None: plain update
       - monadic = Some t: monadic update and t=M<A>
       Dafny also allows :- V, which corresponds to a monadic return, but we do not allow that.
    *)
    and UpdateRHS = { df: Expr; monadic: Type option }

    (* a receiver is the lhs of the . operator when accessing child declarations
    *)
    and Receiver =
        // reference to a static child in a class/module
        | StaticReceiver of ClassType
        // reference to a dynamic child in an object of a class/datatype
        | ObjectReceiver of Expr

    and Quantifier =
        | Forall
        | Exists
        override this.ToString() =
            match this with
            | Forall -> "forall"
            | Exists -> "exists"

    // meta-information
    and Meta = { position: Position option }
    // position in a source file, essentially the same as Microsoft.Boogie.IToken
    and Position =
        { filename: String
          pos: int
          line: int
          col: int }
        override this.ToString() =
            $"{this.filename}@{this.line.ToString()}:{this.col.ToString()}"

    // ***** auxiliary methods

    let emptyMeta = { position = None }

    /// wrapping lists of expressions in a block
    let listToExpr (es: Expr list) : Expr =
        if es.Length = 1 then
            es.Head
        else
            EBlock es

    /// unwrapping lists of expressions in a block
    let exprToList (b: Expr) : Expr list =
        match b with
        | EBlock es -> es
        | e -> [ e ]

    /// s = t
    let EEqual(s:Expr,t:Expr) = EBinOpApply("Eq", s, t)
    /// conjunction of some expressions
    let EConj(es: Expr list) =
        if es.IsEmpty then EBool true
        else List.fold (fun sofar next -> EBinOpApply("And", sofar, next)) es.Head es.Tail
    
    // True if a datatype is simply an enum, i.e.,
    // it has more than one constructor---all without arguments, and no type parameters
    let isEnum (d: Decl) =
        match d with
        | Datatype (_, [], ctors, _, _) -> List.forall (fun c -> c.ins.IsEmpty) ctors
        | _ -> false

    // children of a declaration
    let rec declChildren (d: Decl) : Decl list =
        match d with
        | Module (_, ds, _) -> ds
        | Datatype (_, _, _, ds, _) -> ds
        | Class (_, _, _, _, ds, _) -> ds
        | _ -> error "not a child-bearing declaration"

    /// name of a local declaration
    let localDeclName (l: LocalDecl) = l.name
    /// type of a local Declaration
    let localDeclType (l: LocalDecl) = l.tp
    /// EVar referencing a local Declaration
    let localDeclTerm (l: LocalDecl) = EVar(l.name)

    /// makes a plain update := e
    let plainUpdate (e: Expr) = { df = e; monadic = None }
    /// makes pattern-match case c(x1,...,xn) => bd for a constructor c
    let plainCase(c:Path, lds: LocalDecl list, bd: Expr): Case =
        /// type arguments are empty because there is no matching on types
        let pat = EConstructorApply(c, [], List.map localDeclTerm lds)
        {vars = lds; pattern = pat; body = bd}

    // local variables introduced by an expression (relevant when extending the context during traversal)
    // also defines which variables are visible to later statements in the same block
    let exprDecl (e: Expr) : LocalDecl list =
        match e with
        | EDecls (ds) -> List.map (fun (x, _) -> x) ds
        | EDeclChoice (d, _) -> [ d ]
        | _ -> []

    // local variables introduced by the output specification of a method
    let outputDecls (o: OutputSpec) : LocalDecl list =
        match o with
        | OutputType _ -> []
        | OutputDecls (ds,_) -> ds

    // name of the tester method generator for constructor with name s
    let testerName (s: string) = s + "?"
    (* Some declarations have valid members that are not explicitly declared in the body.``.. ..``
       These can be seen as auto-generated by Dafny.
       They do not appear in the syntax tree, but references to them appear like for other members.
       For now, we only return the headers and use ESkipped for the bodies.

       These are at least:
       for a datatype D:
         - selectors a:A for constructor arguments a:A
           If multiple constructors have arguments of same a, they must all have type A.
           If some but not all constructors have an argument with name a,
           the selector is still present but results in a run-time error when called on other values.
         - testers c?:bool for every constructor c
    *)
    let rec implicitChildren (d: Decl) : Decl list =
        let mkField (ld: LocalDecl) =
            Field(ld.name, ld.tp, None, ld.ghost, isStatic = false, isMutable = false, meta = emptyMeta)

        match d with
        | Datatype (_, _, cs, _, _) ->
            let selectors =
                List.collect (fun (c: DatatypeConstructor) -> c.ins) cs
            let testers =
                List.map
                    (fun (c: DatatypeConstructor) -> LocalDecl(testerName c.name,TBool,false))
                    cs
            List.map mkField (List.append (List.distinct selectors) testers)
        | _ -> []

    (* retrieves a declaration in a program by traversing into children, e.g.,
       lookupByPath(p, []): p itself (wrapped as a module)
       lookupByPath(p,["m","d"]): datatype d in module

       precondition: name must exist
    *)
    let rec lookupByPath (prog: Program, path: Path) : Decl =
        if path.isRoot then
            Module(prog.name, prog.decls, emptyMeta)
        else
            // TODO copy over lookup code from YuccaDafnyCompiler to look up in parent classes
            let parentDecl = lookupByPath (prog, path.parent)
            let children = declChildren (parentDecl)

            match List.tryFind (fun (x: Decl) -> x.name = path.name) children with
            | Some d -> d
            | None ->
                let implChildren = (implicitChildren parentDecl)

                match List.tryFind (fun (x: Decl) -> x.name = path.name) implChildren with
                | Some (d) -> d
                | None -> error $"{path} not valid in {prog.name}"
    (* as above, but returns a constructor *)
    let lookupConstructor (prog: Program, path: Path) : DatatypeConstructor =
        match lookupByPath (prog, path.parent) with
        | Datatype (_, _, ctrs, _, _) -> List.find (fun c -> c.name = path.name) ctrs
        | _ -> error $"parent not a datatype: {path}"


    (* ***** contexts: built during traversal and used for lookup of iCodeIdentifiers

       A Context stores an entire program plus information about where we are during its traversal:
       - prog: the program
       - currentDecl: path to the declarations into which we have traversed, e.g.,
         []: toplevel of program
         ["m", "d"]: in datatype d in module m
       - tpvars: type parameters of enclosing declarations (inner most last)
       - vars: local variables that have been declared (most recent last)

       invariant: currentDecl is always a valid path in prog, i.e., lookupByPath succeeds for every prefix of openDecls
    *)
    type Context(prog: Program, currentDecl: Path, tpvars: string list, vars: LocalDecl list) =
        // convenience constructor and accessor methods
        new(p: Program) = Context(p, Path([]), [], [])
        member this.prog = prog
        member this.currentDecl = currentDecl
        member this.tpvars = tpvars
        member this.vars = vars
        member this.lookupCurrent() = lookupByPath (prog, currentDecl)

        (* lookup of a type variable by name
           precondition: name must exist in the current context
           (which it always does for names encountered while traversing well-typed programs)
        *)
        member this.lookupTpvar(n: string) =
            let dO =
                List.tryFind (fun x -> x = n) (List.rev tpvars)

            match dO with
            | None -> error $"type variable {n} not visible {this}"
            | Some t -> t
        (* lookup of a local variable declaration by name
           precondition: name must exist in the current context
           (which it always does for names encountered while traversing well-typed programs)
        *)
        member this.lookupLocalDecl(n: string) : LocalDecl =
            match this.lookupLocalDeclO (n) with
            | None ->
                error $"variable {n} not visible {this}"
                LocalDecl(n,TUnimplemented,false)
            | Some t -> t

        member this.lookupLocalDeclO(n: string) : LocalDecl option =
            List.tryFind (fun (x: LocalDecl) -> x.name = n) (List.rev vars)

        // short string rendering
        override this.ToString() =
            "in declaration "
            + currentDecl.ToString()
            + (match this.lookupCurrent().meta.position with
               | Some p -> "(" + p.ToString() + ")"
               | _ -> "")
            + " with type variables "
            + listToString (tpvars, ",")
            + " and variables "
            + listToString (List.map localDeclName vars, ", ")

        // convenience method for creating a new context when traversing into a child declaration
        member this.enter(n: string) : Context =
            Context(prog, currentDecl.child (n), tpvars, vars)
        // convenience method for adding variable declarations to the context
        member this.addTpvars(ns: string list) : Context =
            Context(prog, currentDecl, List.append tpvars ns, vars)

        member this.add(ds: LocalDecl list) : Context =
            Context(prog, currentDecl, tpvars, List.append vars ds)
        // abbreviation for a single non-ghost local variable
        member this.add(n: string, t: Type) : Context =
            this.add [LocalDecl(n,t,false)]

    (* ***** printer for the language above

       This is implemented as a class so that we can use state for indentation or overriding for variants.
       A new instance should be created for every print job.
    *)
    // F# has string interpolation now, so this code could be made more readable
    type Printer() =
        let UNIMPLEMENTED = "<UNIMPLEMENTED>"
        let mutable indentLevel = 0

        let indent () =
            listToString (List.map (fun _ -> "  ") [ 2 .. indentLevel ], "")

        member this.prog(p: Program) = this.decls p.decls

        member this.tpvars(ns: string list) =
            if ns.IsEmpty then
                ""
            else
                "[" + listToString (ns, ", ") + "]"

        member this.decls(ds: Decl list) =
            indentLevel <- indentLevel + 1
            let ind = indent ()

            let s =
                listToString (List.map (fun d -> ind + (this.decl d) + "\n") ds, "")

            indentLevel <- indentLevel - 1
            s
        // array dimensions/indices
        member this.dims(ds: Expr list) = "[" + this.exprsNoBr (ds) + "]"
        member this.meta(_: Meta) = ""

        member this.decl(d: Decl) =
            match d with
            | Module (n, ds, a) ->
                "module "
                + (this.meta a)
                + n
                + "\n"
                + (this.decls ds)
            | Datatype (n, tpvs, cons, ds, a) ->
                let consS = List.map this.datatypeConstructor cons

                "datatype "
                + (this.meta a)
                + n
                + (this.tpvars tpvs)
                + " = "
                + listToString (consS, " | ")
                + "\n"
                + (this.decls ds)
            | Class (n, isTrait, tpvs, p, ds, a) ->
                if isTrait then "trait " else "class "
                + (this.meta a)
                + n
                + (this.tpvars tpvs)
                + if p.IsEmpty then
                      ""
                  else
                      (" extends "
                       + listToString (List.map this.classType p, ",")
                       + " ")
                + " {\n"
                + (this.decls ds)
            | TypeDef (n, tpvs, sup, predO, isNew, _) ->
                (if isNew then "newtype " else "type ")
                + n
                + (this.tpvars tpvs)
                + " = "
                + (this.tp sup)
                + (match predO with
                   | Some (x, p) -> " where " + x + "." + (this.expr p)
                   | None -> "")
            | Field (n, t, e, _, _, _, a) ->
                "field "
                + (this.meta a)
                + n
                + ": "
                + (this.tp t)
                + " = "
                + Option.fold (fun _ -> this.expr) "" e
            | Method (isL, n, tpvs, ins, outs, b, _, _, _) ->
                let outsS = this.outputSpec outs
                (if isL then "lemma " else "method ")
                + n
                + (this.tpvars tpvs)
                + (this.inputSpec ins)
                + ": "
                + outsS
                + " = \n"
                + Option.fold (fun _ -> this.expr) "<empty body>" b
            | ClassConstructor (n, tpvs, ins, b, a) ->
                "constructor "
                + (this.meta a)
                + n
                + (this.tpvars tpvs)
                + (this.localDecls ins)
                + " = \n"
                + Option.fold (fun _ -> this.expr) "<empty body>" b
            | Export p -> "export " + p.ToString()
            | DUnimplemented -> UNIMPLEMENTED

        member this.inputSpec(ins: InputSpec) =
            match ins with
            | InputSpec(lds,rs) -> this.localDecls lds + " " + this.conditions(true, rs)

        member this.outputSpec(outs: OutputSpec) =
            match outs with
            | OutputType (t,es) -> this.tp t + " " + this.conditions(false, es)
            | OutputDecls (lds,es) -> this.localDecls lds + " " + this.conditions(false, es)
        
        member this.conditions(require: bool, cs: Condition list) =
            listToString(List.map (fun c -> this.condition(require, c)) cs, "\n")

        member this.condition(require: bool, c: Condition) =
            let kw = if require then "requires" else "ensures"
            kw + " " + this.expr c

        member this.datatypeConstructor(c: DatatypeConstructor) = c.name + (this.localDecls c.ins)
        
        member this.tps(ts: Type list) =
            if ts.IsEmpty then
                ""
            else
                "<"
                + listToString (List.map this.tp ts, ",")
                + ">"

        member this.tp(t: Type) = t.ToString()

        member this.exprsNoBr(es: Expr list) =
            listToString (List.map this.expr es, ", ")

        member this.exprs(es: Expr list) = "(" + (this.exprsNoBr es) + ")"

        member this.exprO(eO: Expr option, sep: string) =
            Option.defaultValue ("") (Option.map (fun e -> sep + (this.expr e)) eO)

        member this.expr(e: Expr) =
            let expr = this.expr
            let exprs = this.exprs
            let exprO = this.exprO
            let tp = this.tp
            let tps = this.tps

            match e with
            | EVar n -> n
            | EThis -> "this"
            | ENew (ct, _) -> "new " + this.classType (ct)
            | ENull _ -> "null"
            | EMemberRef (r, m, ts) -> this.receiver (r) + "." + m.name + (tps ts)
            | EBool (v) -> v.ToString()
            | EChar (v) -> "'" + v.ToString() + "'"
            | EString (v) -> "\"" + v.ToString() + "\""
            | EToString (es) -> "\"" + (exprs es) + "\""
            | EInt (v, _) -> v.ToString()
            | EReal (v, _) -> v.ToString()
            | EQuant (q, lds, r, b) ->
                q.ToString()
                + " "
                + this.localDecls (lds)
                + exprO (r, " where ")
                + "."
                + (expr b)
            | ETuple (es) -> exprs es
            | EProj (e, i) -> expr (e) + "." + i.ToString()
            | EFun (vs, _, e) -> "fun " + (this.localDecls vs) + " => " + (expr e)
            | ESet (_, es) -> "set" + (exprs es)
            | ECharAt (s, i) -> (expr s) + this.dims ([ i ])
            | EStringRange (s, f, t) ->
                (expr s)
                + "["
                + exprO (f, "")
                + ".."
                + exprO (t, "")
                + "]"
            | ESeq (_, es) -> "seq" + (exprs es)
            | ESeqAt (s, i) -> (expr s) + "[" + (expr i) + "]"
            | ESeqRange (s, f, t) ->
                (expr s)
                + "["
                + exprO (f, "")
                + ".."
                + exprO (t, "")
                + "]"
            | ESeqUpdate (s, i, e) -> (expr s) + "[" + (expr i) + "] = " + (expr e)
            | EArray (t, d) -> "new " + t.ToString() + this.dims (d)
            | EArrayAt (a, i) -> (expr a) + this.dims (i)
            | EArrayUpdate (a, i, e) -> (expr a) + this.dims (i) + " = " + (expr e)
            | EMapAt (m, e) -> (expr m) + (this.dims [ e ])
            | EMapKeys (e) -> (expr e) + ".Keys"
            | EUnOpApply (op, e) -> op + " " + (expr e)
            | EBinOpApply (op, e1, e2) -> "(" + (expr e1) + " " + op + " " + (expr e2) + ")"
            | EAnonApply (f, es) -> (expr f) + (exprs es)
            | EMethodApply (r, m, ts, es, _) ->
                this.receiver (r)
                + "."
                + m.name
                + (tps ts)
                + (exprs es)
            | EConstructorApply (c, ts, es) -> c.ToString() + (tps ts) + (exprs es)
            | EBlock (es) -> "{" + (this.exprsNoBr es) + "}"
            | ELet (n, t, d, e) ->
                "let "
                + n
                + ":"
                + (tp t)
                + "="
                + (expr d)
                + " in "
                + (expr e)
            | EIf (c, t, e) ->
                "if ("
                + (expr c)
                + ") "
                + (expr t)
                + exprO (e, " else ")
            | EFor (index, init, last, up, body) ->
                let d =
                    EDecls [ (index, Some(plainUpdate init)) ]

                "for ("
                + (expr d)
                + (if up then " to " else " downto ")
                + (expr last)
                + ") "
                + (expr body)
            | EWhile (c, e, l) ->
                let label =
                    match l with
                    | Some l -> sprintf "%s: " l
                    | None -> ""

                sprintf "%swhile (%s)%s" label (expr c) (expr e)
            | EReturn (es) -> "return " + (this.exprsNoBr es)
            | EBreak l ->
                let label =
                    match l with
                    | Some l -> sprintf " %s" l
                    | None -> ""

                sprintf "break%s" label
            | EMatch (e, t, cases, dfltO) ->
                let csS =
                    List.map (fun (c: Case) -> this.case (c)) cases
                let dS = match dfltO with
                         | Some d -> ["_ -> " + expr d]
                         | None -> [] 
                (expr e)
                + ": "
                + (tp t)
                + " match "
                + listToString (csS@dS, " | ")
            | EDecls (ds) ->
                let doOne (ld: LocalDecl, uO: UpdateRHS option) =
                    "var "
                    + (this.localDecl ld)
                    + (Option.defaultValue "" (Option.map this.update uO))

                listToString (List.map doOne ds, ", ")
            | EUpdate (ns, u) -> listToString (ns, ",") + this.update (u)
            | EDeclChoice (ld, e) ->
                "var "
                + (this.localDecl ld)
                + " where "
                + (expr e)
            | EUnimplemented -> UNIMPLEMENTED
            | ETypeConversion (e, toType) -> (expr e) + " as " + (tp toType)
            | EPrint es -> "print" + (String.concat ", " (List.map expr es))

        member this.localDecls(lds: LocalDecl list) =
            "("
            + listToString (List.map this.localDecl lds, ", ")
            + ")"

        member this.update(u: UpdateRHS) =
            let op = if u.monadic.IsSome then ":-" else ":="
            " " + op + " " + (this.expr u.df)

        member this.localDecl(ld: LocalDecl) = ld.name + ": " + (this.tp ld.tp)

        member this.classType(ct: ClassType) =
            ct.path.ToString() + (this.tps ct.tpargs)

        member this.receiver(rcv: Receiver) =
            match rcv with
            | StaticReceiver (ct) -> this.classType (ct)
            | ObjectReceiver (e) -> this.expr e

        member this.case(case: Case) =
            this.expr case.pattern
            + " => "
            + (this.expr case.body)

    // shortcut to create a fresh printer
    let printer () = Printer()
