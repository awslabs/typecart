namespace TypeInjections

// DotNet, for number literals
open System
open System.Numerics
open Microsoft.BaseTypes

// Yucca
open Microsoft.Dafny
open Microsoft.FSharp.Collections
open Utils

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
            | Path ns -> ns
        /// empty path
        member this.isRoot = this.names.IsEmpty
        /// this . n
        member this.child(n: string) =
            if n = "" then
                this
            else
                Path(this.names @ [ n ])
        /// this . ns
        member this.append(ns: Path) =
            Path(
                this.names
                @ List.filter (fun x -> x <> "") ns.names
            )
        /// prefix root component; used for adding "Old", "New", etc.
        member this.prefix(s: string) =
            Path((s + "." + this.names.Head) :: this.names.Tail)
        /// a.b.c ---> a.b
        member this.parent = Path(listDropLast this.names)
        /// a.b.c ---> c
        member this.name = listLast this.names
        /// p = this . rest
        member this.isAncestorOf(p: Path) =
            let l = this.names.Length

            p.names.Length >= l
            && p.names[..l - 1] = this.names
        /// p = rest . this
        member this.isSuffixOf(p: Path) =
            let l = this.names.Length

            p.names.Length >= l
            && p.names[p.names.Length - l..] = this.names
        /// this . that ---> that
        /// this == that == a.b.c ---> c
        member this.relativize(that: Path) =
            if this.names.Length >= 1 && that.names.Length >= 2 && this.names[0] = that.names[0] then
                (Path this.names[1..]).relativize(Path that.names[1..])
            else
                that
        /// (Old.a).b.c == a.b.c == (New.a).b.c
        member this.onlyDifferByPrefix(p: Path) =
            if this.names.Length <> p.names.Length then
                false
            elif this.names.Length = 0 then
                true
            else
                Array.last(this.names[0].Split(".")) = Array.last(p.names[0].Split(".")) &&
                    this.names[1..] = p.names[1..]
        /// dot-separated names
        override this.ToString() = listToString (this.names, ".")

    // meta-information
    [<CustomEquality; NoComparison>]
    type Meta =
        { comment: string option
          position: Position option
          prelude: string
          attributes: Map<string, string list> }
        override this.GetHashCode() = 0
        // we make all Meta objects equal so that they are ignored during diffing
        override this.Equals(that: Object) =
            match that with
            | :? Meta -> true
            | _ -> false
        member this.addAttribute(k: string, v: string list) =
            { this with attributes=this.attributes.Add(k, v) }
    // position in a source file, essentially the same as Microsoft.Boogie.IToken
    and Position =
        { filename: String
          pos: int
          line: int
          col: int }
        override this.ToString() =
            $"{this.filename}@{this.line.ToString()}:{this.col.ToString()}"

    // ***** auxiliary methods
    let emptyMeta =
        { comment = None
          position = None
          prelude = ""
          attributes = Map.empty }

    /// name of nonymous variables
    let anonymous = "_"

    (* toplevel declaration
       The program name corresponds to the package name or root namespace.

       This could be a special case of Decl or even just a Module.
       But for now we keep it separate because:
       - Modules aren't nested for now, and we want to forbid that altogether.
       - We way want to add information here later.
       - It is convenient to have a type of programs and not just a constructor.
    *)
    type Program =
        { name: string
          decls: Decl list
          meta: Meta }

    (* declarations
       Modules and datatypes are child-bearing, i.e., can contain nested declarations.
       Each declaration is named uniquely within its parent.
       Within the program each declaration is uniquely identified.
    *)
    and Decl =
        (* Include "..." is a preprocessor-like intrinsic in dafny that causes dafny to inline a file *)
        | Include of p: Path
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
            tpvars: TypeArg list *
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
        | ClassConstructor of
            name: string *
            tpvars: TypeArg list *
            ins: InputSpec *
            outs: Condition list *
            body: Expr option *
            meta: Meta
        (* Type definitions
           if predicate is given: HOL-style subtype definitions
             else: type synonym
           if isNew: type is not a subtype of the supertype (which must be nat or real and thus tpvars = [])
        *)
        | TypeDef of
            name: string *
            tpvars: TypeArg list *
            super: Type *
            predicate: (string * Expr * Witness) option *
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
            methodType: MethodType *
            name: string *
            tpvars: TypeArg list *
            ins: InputSpec *
            out: OutputSpec *
            modifies: Expr list *
            reads: Expr list *
            decreases: Expr list *
            body: Expr option *
            ghost: bool *
            isStatic: bool *
            isOpaque: bool *
            meta: Meta
        | Import of ImportType
        | Export of ExportType
        // dummy for missing cases
        | DUnimplemented
        member this.meta =
            match this with
            | Module (_, _, meta) -> meta
            | Datatype (_, _, _, _, meta) -> meta
            | Class (_, _, _, _, _, meta) -> meta
            | ClassConstructor (_, _, _, _, _, meta) -> meta
            | Method (_, _, _, _, _, _, _, _, _, _, _, _, meta) -> meta
            | Field (_, _, _, _, _, _, meta) -> meta
            | TypeDef (_, _, _, _, _, meta) -> meta
            | _ -> emptyMeta

        member this.name =
            match this with
            | Module (n, _, _) -> n
            | Datatype (n, _, _, _, _) -> n
            | Class (n, _, _, _, _, _) -> n
            | ClassConstructor (n, _, _, _, _, _) -> n
            | Method (_, n, _, _, _, _, _, _, _, _, _, _, _) -> n
            | Field (n, _, _, _, _, _, _) -> n
            | TypeDef (n, _, _, _, _, _) -> n
            | Import _
            | Export _
            | Include _
            | DUnimplemented -> "" // check if this causes problems
        // type arguments of a declaration
        member this.tpvars =
            match this with
            | Module _ -> []
            | Datatype (_, tpvs, _, _, _) -> tpvs
            | Class (_, _, tpvs, _, _, _) -> tpvs
            | TypeDef (_, tpvs, _, _, _, _) -> tpvs
            | Field _ -> []
            | Method (_, _, tpvs, _, _, _, _, _, _, _, _, _, _) -> tpvs
            | ClassConstructor (_, tpvs, _, _, _, _) -> tpvs
            | Import _ -> []
            | Export _ -> []
            | Include _ -> []
            | DUnimplemented -> []

        member this.children =
            match this with
            | Module (_, ds, _) -> ds
            | Datatype (_, _, _, ds, _) -> ds
            | Class (_, _, _, _, ds, _) -> ds
            | _ -> []

        member this.filterChildren(mustPreserve: Decl -> bool) =
            let f ds = List.filter (mustPreserve) ds

            match this with
            | Module (x, ds, y) -> Module(x, f ds, y)
            | Datatype (a, b, c, ds, d) -> Datatype(a, b, c, ds, d)
            | Class (a, b, c, d, ds, e) -> Class(a, b, c, d, ds, e)
            | _ -> this

        member this.isModule() =
            match this with
            | Module _ -> true
            | _ -> false
        
        member this.updateMeta(meta: Meta) =
            match this with
            | Module (a, b, _) -> Module(a, b, meta)
            | Datatype (a, b, c, d, _) -> Datatype(a, b, c, d, meta)
            | Class (a, b, c, d, e, _) -> Class(a, b, c, d, e, meta)
            | ClassConstructor (a, b, c, d, e, _) -> ClassConstructor(a, b, c, d, e, meta)
            | Method (a, b, c, d, e, f, g, h, i, j, k, l, _) -> Method(a, b, c, d, e, f, g, h, i, j, k, l, meta)
            | Field (a, b, c, d, e, f, _) -> Field(a, b, c, d, e, f, meta)
            | TypeDef (a, b, c, d, e, _) -> TypeDef(a, b, c, d, e, meta)
            | _ -> this
    
    and Witness =
        | CompiledZero
        | OptOut

    // ""/+/-/*/! for non/co/contra/co/non-variant ("" and + are strict); true for equality required; true for non-heap based
    and TypeArg = string * (string * bool * bool)
    /// Three Dafny method types. This is going to matter when pretty-printing, since
    /// Dafny distinguishes the set of syntaxes allowed when printing different methods.
    and MethodType =
        | IsMethod
        | IsFunctionMethod
        | IsFunction
        | IsLemma
        | IsLeastLemma
        | IsGreatestLemma
        | IsPredicate
        | IsLeastPredicate
        | IsGreatestPredicate
        | IsPredicateMethod
        member this.isGhost() =
            match this with
            | IsMethod
            | IsFunctionMethod
            | IsPredicateMethod -> false
            | IsFunction
            | IsLemma
            | IsPredicate
            | IsLeastLemma
            | IsGreatestLemma
            | IsLeastPredicate
            | IsGreatestPredicate -> true

        override this.ToString() =
            match this with
            | IsMethod -> "method"
            | IsFunctionMethod -> "function"
            | IsPredicateMethod -> "predicate"
            | IsFunction -> "function"
            | IsLemma -> "lemma"
            | IsPredicate -> "predicate"
            | IsLeastLemma -> "least lemma"
            | IsGreatestLemma -> "greatest lemma"
            | IsLeastPredicate -> "least predicate"
            | IsGreatestPredicate -> "greatest predicate"

    and ExportType(provides: Path list, reveals: Path list) =
        new() = ExportType([], [])
        member this.provides = provides
        member this.reveals = reveals

        override this.ToString() =
            let lts (ps: Path list) = listToString (ps, ", ")

            match this.provides, this.reveals with
            | [], [] -> ""
            | _ ->
                "export \n"
                + (match this.provides with
                   | [] -> ""
                   | _ -> "  provides " + (lts this.provides))
                + "\n"
                + (match this.reveals with
                   | [] -> ""
                   | _ -> "  reveals " + (lts this.reveals))



        override this.Equals(that) =
            match that with
            | :? ExportType as that ->
                this.provides.Equals(that.provides)
                && this.reveals.Equals(that.reveals)
            | _ -> false

        override this.GetHashCode() = this.ToString().GetHashCode()

    and ImportType =
        | ImportDefault of opened: bool * dir: Path
        | ImportEquals of opened: bool * lhsDir: string * rhsDir: Path
        override this.ToString() =
            match this with
            | ImportDefault (o, p) -> "import " + (if o then "opened " else "") + p.ToString()
            | ImportEquals (o, lhs, rhs) ->
                "import "
                + (if o then "opened " else "")
                + lhs.ToString()
                + " = "
                + rhs.ToString()
        member this.isOpened() =
            match this with
            | ImportDefault (o, _)
            | ImportEquals (o, _, _) -> o
        // for ImportEquals, compare rhsDir since it is the given name to the import.
        member this.pathEquals(p': Path) =
            match this with
            | ImportDefault (_, p)
            | ImportEquals (_, _, p) -> p.Equals(p')
        // return path of import. For ImportEquals, return path of rhs
        member this.getPath() =
            match this with
            | ImportDefault (_, p)
            | ImportEquals (_, _, p) -> p

        member this.prefix(pre: string) =
            match this with
            | ImportDefault (o, p) -> ImportDefault(o, p.prefix (pre))
            | ImportEquals (o, lhs, p) -> ImportEquals(o, lhs, p.prefix (pre))
    (* types
       We do not allow module inheritance or Dafny classes.
       Therefore, there is no subtyping except for numbers.
    *)
    and Type =
        // built-in base types
        | TUnit
        | TBool
        | TChar
        | TString of Bound
        | TNat of Bound
        | TInt of Bound
        | TReal of Bound
        | TBitVector of int
        // built-in type operators
        | TTuple of Type list
        | TFun of Type list * Type
        | TSeq of Bound * Type
        | TSet of Bound * Type
        | TMap of Bound * Type * Type
        | TArray of Bound * string * Type // array of any dimensions (string "array2" means 2 dimensions)
        | TObject // supertype of all classes
        | TNullable of Type
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
                    "<" + listToString (ts, ",") + ">"

            let product (ts: Type list) =
                if ts.Length = 1 then
                    ts.Head.ToString()
                else
                    "(" + listToString (ts, ",") + ")"

            match this with
            | TUnit -> "unit"
            | TBool -> "bool"
            | TInt b -> "int" + b.ToString()
            | TNat b -> "nat" + b.ToString()
            | TChar -> "char"
            | TString b -> "string" + b.ToString()
            | TReal b ->
                match b with
                | Bound (Some 32) -> "float"
                | Bound (Some 64) -> "double"
                | _ -> "real"
            | TBitVector (w) -> "bv" + w.ToString()
            | TVar n -> n
            | TApply (op, args) -> (String.concat "." op.names) + (tps args)
            | TTuple (ts) -> product ts
            | TFun (ins, out) -> (product ins) + "->" + (out.ToString())
            | TSeq (b, t) -> "seq" + b.ToString() + (tps [ t ])
            | TSet (b, t) -> "set" + b.ToString() + (tps [ t ])
            | TArray (b, n, t) -> n + b.ToString() + (tps [ t ])
            | TMap (b, d, r) -> "map" + b.ToString() + (tps [ d; r ])
            | TObject -> "object"
            | TNullable t -> t.ToString() + "?"
            | TUnimplemented -> "UNIMPLEMENTED"

    // for size-limited version of types defined in Yucca's TypeUtil, gives the size in bits
    // See DafnyToYIL for the possibly bound values, usually 32 or 64
    and Bound =
        | Bound of int option
        override this.ToString() =
            match this with
            | Bound (Some i) -> i.ToString()
            | Bound None -> ""

    (* typed variable declaration used in method input/output, binders, and local variables declarations
       All of those can be ghosts, i.e., only needed for specifications and proofs.
       Those can be removed when compiling for computation.
    *)
    and LocalDecl =
        | LocalDecl of string * Type * bool
        member this.name =
            match this with
            | LocalDecl (n, _, _) -> n

        member this.tp =
            match this with
            | LocalDecl (_, t, _) -> t

        member this.ghost =
            match this with
            | LocalDecl (_, _, g) -> g

        member this.isAnonymous() = this.name = anonymous


    (* pre/postcondition of a method/lemma
       A "requires" statement may have a label.
     *)
    and Condition = Expr * string option

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
       When patterns contains more than one pattern, it is a disjunctive pattern (pattern1 | ... | patternn).
     *)
    and Case =
        { vars: LocalDecl list
          patterns: Expr list
          body: Expr }

    /// input specification: typed variables and preconditions
    and InputSpec =
        | InputSpec of LocalDecl list * Condition list
        member this.decls =
            match this with
            | InputSpec (ds, _) -> ds

        member this.conditions =
            match this with
            | InputSpec (_, cs) -> cs

    /// output specification: typed variables and postconditions
    // to avoid case distinctions, the case of an unnamed output type is represented as a single anonymous variable
    and OutputSpec =
        | OutputSpec of LocalDecl list * Condition list
        member this.decls =
            match this with
            | OutputSpec (ds, _) -> ds
        /// the unnamed output type if any
        member this.outputType =
            match this.decls with
            | [ ld ] when ld.isAnonymous () -> Some ld.tp
            | _ -> None
        /// the output declarations (i.e., without the dummy declaration for an output type)
        member this.namedDecls =
            this.decls
            |> List.filter (fun ld -> not (ld.isAnonymous ()))

        member this.conditions =
            match this with
            | OutputSpec (_, cs) -> cs

    (* a reference to a module or class with all its type parameters instantiated
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
        | EArray of tp: Type * dim: Expr list * init: ArrayInitializer
        // built-in values of base types (literals)
        // Dafny represents nat literals as TInt literals even if the context demands it have type TNat.
        | EBool of bool
        // Dafny represents char and string literals as strings that include the escape characters as separate characters.
        | EChar of string
        | EString of string
        | EToString of expr: Expr list
        | EInt of BigInteger * tp: Type
        | EReal of BigDec * tp: Type
        // Dafny allows quantifiers in computations if the domain is finite; cond is a predicate that restricts the domain of the bound variables
        | EQuant of quant: Quantifier * ld: LocalDecl list * cond: Expr option * body: Expr
        | EOld of Expr // used in ensures conditions of methods in classes to refer to previous state
        | ETuple of elems: Expr list
        | EProj of tuple: Expr * index: int
        | EFun of vars: LocalDecl list * cond: Condition option * out: Type * body: Expr
        // *** introduction/elimination forms for built-in type operators
        | ESet of tp: Type * elems: Expr list
        | ESetComp of lds: LocalDecl list * p: Expr * body: Expr // set comprehension {x in lds | p(lds) : f(x)}
        | ESeq of tp: Type * elems: Expr list
        | ESeqConstr of tp: Type * length: Expr * init: Expr // builds sequence init(0), ..., init(length-1)
        | EMapKeys of map: Expr
        | EMapValues of map: Expr
        | EMapDisplay of map: (Expr * Expr) list // explicit map represented as a list
        // map comprehension where tL is an expression over the preimage and tR is an expression mapping preimage to
        // image. If tL = Some tLF, generates the map tLF(p(lds)) -> tR(p(lds)). Otherwise, generates the map
        // p(lds) -> tR(p(lds)).
        | EMapComp of lds: LocalDecl list * p: Expr * tL: Expr Option * tR: Expr
        /// Dafny's ad hoc polymorphic selection expression
        /// expr can be anything sequence-like, e.g., sequence, map, string, tp stores its type
        /// returns element or slice depending on which indices are given; redundantly stored in 'element'
        /// these are disambiguated into separate constructors in the YuccaCompiler
        | ESeqSelect of expr: Expr * tp: Type * element: bool * fromIndex: Expr option * toIndex: Expr option
        /// multi-dim array access
        | EMultiSelect of expr: Expr * indices: Expr list
        | ESeqUpdate of seq: Expr * index: Expr * df: Expr
        | EArrayUpdate of array: Expr * index: Expr list * value: Expr // in-place array update
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
        /// datatype constructors
        | EConstructorApply of cons: Path * tpargs: Type list * args: Expr list
        /// type conversion (e as t)
        | ETypeConversion of expr: Expr * toType: Type
        /// type test (e is t)
        | ETypeTest of Expr * Type
        // *** control flow etc.
        | EBlock of exprs: Expr list
        | ELet of vars: LocalDecl list * exact: bool * orfail: bool * lhs: Expr list * df: Expr list * body: Expr // not exact = non-deterministic
        | EIf of cond: Expr * thn: Expr * els: Expr option // cond must not have side-effects; els non-optional if this is an expression; see also flattenIf
        | EAlternative of conds: Expr list * bodies: Expr list // if case cond1 => body1 case cond2 => body2
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
        *)
        | EDecls of vars: LocalDecl list * lhs: Expr list * rhs: UpdateRHS list
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
        | EAssert of expr: Expr * proof: Expr option
        | EExpect of Expr // dafny expect statement (non-ghost variant of assert statement)
        | EAssume of Expr // dafny implication introduction
        | EReveal of Expr list // dafny `reveal ... ;` proof directive
        | ECommented of string * Expr
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
    
    (* array initializers:
       Uninitialized: new int[5,6]
       ValueList: new int[][2,3,5,7,11] (equivalent to new int[5][2,3,5,7,11], must be 1-dimensional)
       ComprehensionLambda: new int[5](i => i*i)
    *)
    and ArrayInitializer =
        | Uninitialized
        | ValueList of Expr list
        | ComprehensionLambda of Expr

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

    // result type for imports analysis
    type ModuleImports(modulePath: Path, imports: ImportType list) =
        new() = ModuleImports(Path [], [])
        member this.modulePath = modulePath
        member this.imports = imports
        member this.setModulePath(modulePath: Path) = ModuleImports(modulePath, this.imports)

        member this.addImport(importPath: Path, importType: ImportType) =
            ModuleImports(this.modulePath, importType :: this.imports)

    // auxiliary methods
    /// dummy program
    let emptyProgram =
        { name = ""
          decls = []
          meta = emptyMeta }
    
    /// replace the top-level Path of a Receiver during DafnyToYIL
    let replaceReceiverPath(r: Receiver, path: Path) : Receiver =
        match r with
        | StaticReceiver classType -> StaticReceiver({path=path; tpargs =  classType.tpargs})
        | _ -> r
    
    /// replace the top-level Path of an Expr during DafnyToYIL
    let replacePath (e: Expr, path: Path) : Expr =
        match e with
        | EConstructorApply(_, tpargs, args) -> EConstructorApply(path, tpargs, args)
        | EMethodApply(receiver, method, tpargs, args, ghost) ->
            EMethodApply(replaceReceiverPath(receiver, path), method, tpargs, args, ghost)
        | _ -> e
    

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

    /// wraps in a block if not yet a block
    let block (b: Expr) : Expr =
        match b with
        | EBlock _ -> b
        | _ -> EBlock [ b ]

    /// invariant type argument given by name
    let plainTypeArg n = (n, ("", false, false))

    /// the corresponding list of TVars
    let typeargsToTVars (tvs: TypeArg list) = List.map (fun (n, _) -> TVar n) tvs

    let NoBound = Bound None
    let Bound8 = Bound(Some 8)
    let Bound16 = Bound(Some 16)
    let Bound32 = Bound(Some 32)
    let Bound64 = Bound(Some 64)
    /// Some Java-specific types.
    let Bound31 = Bound(Some 31)
    let Bound63 = Bound(Some 63)

    /// empty command
    let ESKip = EBlock []

    /// s = t
    let EEqual (s: Expr, t: Expr) = EBinOpApply("EqCommon", s, t)
    /// conjunction of some expressions
    let EConj (es: Expr list) =
        if es.IsEmpty then
            EBool true
        else
            List.fold (fun sofar next -> EBinOpApply("And", sofar, next)) es.Head es.Tail

    let EDisj (es: Expr list) =
        if es.IsEmpty then
            EBool false
        else
            List.fold (fun sofar next -> EBinOpApply("Or", sofar, next)) es.Head es.Tail

    /// the special variable _ (must only be used in patterns)
    let EWildcard = EVar anonymous

    // True if a datatype is simply an enum, i.e.,
    // it has more than one constructor---all without arguments, and no type parameters
    let isEnum (d: Decl) =
        match d with
        | Datatype (_, [], ctors, _, _) -> List.forall (fun c -> c.ins.IsEmpty) ctors
        | _ -> false

    /// OutputSpec with a plain return type
    let outputType (t: Type, cs: Condition list) =
        OutputSpec([ LocalDecl(anonymous, t, false) ], cs)

    /// name of a local declaration
    let localDeclName (l: LocalDecl) = l.name
    /// type of a local Declaration
    let localDeclType (l: LocalDecl) = l.tp
    /// EVar referencing a local Declaration
    let localDeclTerm (l: LocalDecl) = EVar(l.name)

    /// makes a plain update := e
    let plainUpdate (e: Expr) = { df = e; monadic = None }
    /// makes pattern-match case c(x1,...,xn) => bd for a constructor c
    let plainCase (c: Path, lds: LocalDecl list, bd: Expr) : Case =
        // Use prefix to explicitly detect anonymous tuple constructors here.
        let lts = List.map localDeclTerm lds
        // type arguments to EConstructorApply(...) are empty because there is no matching on types
        let pat = EConstructorApply(c, [], lts)
        { vars = lds; patterns = [ pat ]; body = bd }

    // local variables introduced by an expression (relevant when extending the context during traversal)
    // also defines which variables are visible to later statements in the same block
    let exprDecl (e: Expr) : LocalDecl list =
        match e with
        | EDecls (d, _, _) -> d
        | EDeclChoice (d, _) -> [ d ]
        | _ -> []

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
                List.map (fun (c: DatatypeConstructor) -> LocalDecl(testerName c.name, TBool, false)) cs

            List.map mkField (List.append (List.distinct selectors) testers)
        | Module (_, decls, _) -> List.collect implicitChildren decls
        | _ -> []

    (* retrieves all nested declarations in a program that lead to a given one
       precondition: name must exist
       postcondition: not empty
    *)
    let rec lookupAncestorsByPath (prog: Program, path: Path) : Decl list =
        if path.isRoot then
            [ Module(prog.name, prog.decls, emptyMeta) ]
        else
            // if we use classes, maybe copy over lookup code from YuccaDafnyCompiler to look up in parent classes
            let ancestorDecls =
                lookupAncestorsByPath (prog, path.parent)

            let parentDecl = ancestorDecls.Head
            let children = parentDecl.children

            match List.tryFind (fun (x: Decl) -> x.name = path.name) children with
            | Some d -> d :: ancestorDecls
            | None ->
                let implChildren = (implicitChildren parentDecl)

                match List.tryFind (fun (x: Decl) -> x.name = path.name) implChildren with
                | Some d -> d :: ancestorDecls
                | None -> error $"Path [{path}] not valid in {prog.name}"
    (* retrieves a declaration in a program by traversing into children, e.g.,
       lookupByPath(p, []): p itself (wrapped as a module)
       lookupByPath(p,["m","d"]): datatype d in module

       precondition: name must exist
    *)
    let lookupByPath (prog: Program, path: Path) : Decl = lookupAncestorsByPath(prog, path).Head

    (* as above, but returns a constructor *)
    let lookupConstructor (prog: Program, path: Path) : DatatypeConstructor =
        match lookupByPath (prog, path.parent) with
        | Datatype (_, _, ctrs, _, _) -> List.find (fun c -> c.name = path.name) ctrs
        | _ -> error $"parent not a datatype: {path}"

    /// used in Context to track where we are
    /// adjust this if we ever need to track the position in a more refined way, e.g.,
    /// to track if we are in the return position of an expression
    type ContextPosition =
        | BodyPosition
        | InForLoopInitializer
        | InForLoopBody
        | PatternPosition
        | OtherPosition

    (* ***** contexts: built during traversal and used for lookup of iCodeIdentifiers

       A Context stores an entire program plus information about where we are during its traversal:
       - prog: the program
       - currentDecl: path to the declarations into which we have traversed, e.g.,
         []: toplevel of program
         ["m", "d"]: in datatype d in module m
       - tpvars: type parameters of enclosing declarations (inner most last)
       - vars: local variables that have been declared (most recent last)
       - pos: tracks if we are in the body of a method

       invariant: currentDecl is always a valid path in prog, i.e., lookupByPath succeeds for every prefix

       TODO: remove importPaths and just collect imports from the AST
    *)
    type Context
        (
            prog: Program,
            currentDecl: Path,
            tpvars: TypeArg list,
            vars: LocalDecl list,
            pos: ContextPosition,
            importPaths: ImportType list,
            thisDecl: LocalDecl option
        ) =
        /// convenience constructor and accessor methods
        new(p: Program) = Context(p, Path([]), [], [], OtherPosition, [], None)
        /// dummy context, use carefully
        new() = Context(emptyProgram, Path([]), [], [], OtherPosition, [], None)

        member this.prog = prog
        member this.currentDecl = currentDecl
        member this.tpvars = tpvars
        member this.vars = vars
        member this.lookupCurrent() = lookupByPath (prog, currentDecl)
        member this.lookupByPath(p: Path) = lookupByPath (prog, p)
        member this.pos = pos
        
        member this.thisDecl = thisDecl
        
        member this.pathWithoutPseudoModule() =
            let p = this.currentDecl
            if p.names.Length = 0 then
                p
            else if p.names[0].Contains(".") then
                let topName = p.names[0].Split(".")
                assert (topName.Length = 2)
                Path (topName[1]::p.names[1..])
            else
                p

        member this.modulePath() =
            let ancs =
                listDropLast (lookupAncestorsByPath (prog, currentDecl)) // drop pseudo-module for whole program

            let firstModO =
                ancs
                |> List.tryFindIndex (fun (d: Decl) -> d.isModule ())

            if firstModO.IsNone then
                Path []  // global
            else
                let modNames =
                    ancs.GetSlice(firstModO, None)
                    |> List.map (fun d -> d.name)

                Path(List.rev modNames)

        member this.importPaths = importPaths

        /// lookup of a type variable by name
        /// precondition: name must exist in the current context
        /// (which it always does for names encountered while traversing well-typed programs)
        member this.lookupTpvar(n: string) =
            let dO =
                List.tryFind (fun x -> fst x = n) (List.rev tpvars)

            match dO with
            | None -> error $"type variable {n} not visible {this}"
            | Some t -> t
        /// lookup of a local variable declaration by name
        /// precondition: name must exist in the current context
        /// (which it always does for names encountered while traversing well-typed programs)
        member this.lookupLocalDecl(n: string) : LocalDecl =
            match this.lookupLocalDeclO (n) with
            | None ->
                error $"variable {n} not visible {this}"
                LocalDecl(n, TUnimplemented, false)
            | Some t -> t

        member this.lookupLocalDeclO(n: string) : LocalDecl option =
            List.tryFind (fun (x: LocalDecl) -> x.name = n) (List.rev vars)

        /// short string rendering
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

        member this.currentMeta() = this.lookupCurrent().meta

        /// convenience method for creating a new context when traversing into a child declaration
        member this.enter(n: string) : Context =
            Context(prog, currentDecl.child (n), tpvars, vars, pos, importPaths, thisDecl)
        /// convenience method for adding type variable declarations to the context
        member this.addTpvars(ns: string list) : Context =
            Context(prog, currentDecl, List.append tpvars (List.map plainTypeArg ns), vars, pos, importPaths, thisDecl)
        /// convenience method for adding type variable declarations to the context
        member this.addTpvars(tvs: TypeArg list) : Context =
            Context(prog, currentDecl, List.append tpvars tvs, vars, pos, importPaths, thisDecl)

        member this.add(ds: LocalDecl list) : Context =
            Context(prog, currentDecl, tpvars, List.append vars ds, pos, importPaths, thisDecl)
        // abbreviation for a single non-ghost local variable
        member this.add(n: string, t: Type) : Context = this.add [ LocalDecl(n, t, false) ]
        
        // set the LocalDecl for "this"
        member this.setThisDecl(d: LocalDecl) : Context =
            Context(prog, currentDecl, tpvars, vars, pos, importPaths, Some(d))
        
        // unset the LocalDecl for "this"
        member this.unsetThisDecl(d: LocalDecl) : Context =
            Context(prog, currentDecl, tpvars, vars, pos, importPaths, None)


        /// remembers where we are
        member this.setPos(p: ContextPosition) =
            Context(prog, currentDecl, tpvars, vars, p, importPaths, thisDecl)

        member this.enterBody() = this.setPos (BodyPosition)

        // add and remove imports
        member this.addImport(importType: ImportType) =
            Context(prog, currentDecl, tpvars, vars, pos, importType :: importPaths, thisDecl)
        member this.clearImport() =
            Context(prog, currentDecl, tpvars, vars, pos, [], thisDecl)

    (* ***** printer for the language above

       This is implemented as a class so that we can use state for indentation or overriding for variants.
       A new instance should be created for every print job.

       strict: print parsable Dafny syntax; if set, the passed contexts must be correct
    *)
    // F# has string interpolation now, so this code could be made more readable
    type Printer(strict: bool) =
        let UNIMPLEMENTED = "<UNIMPLEMENTED>"
        let indentString = "  "

        let indented (s: string, braced: Boolean) =
            let s =
                ("\n" + s).Replace("\n", "\n" + indentString)

            if braced then "{" + s + "\n}" else s

        let indentedBraced (s: string) = indented (s, true)

        member this.prog(p: Program, pctx: Context) =
            // Print out includes first because Dafny enforces this.
            // For future work, consider making includes meta-information instead of
            // AST information, as this along with the design of Dafny includes as a
            // preprocessor-level syntax construct.
            let iPath (p: Path) =
                let toSysPath (Path plist) = String.concat "/" plist
                "include " + "\"" + toSysPath (p) + "\""

            let includes =
                List.collect
                    (function
                    | Include p -> [ iPath p ]
                    | _ -> [])
                    p.decls
                |> String.concat "\n"

            includes
            + "\n"
            + if not (p.meta.prelude = "") then
                  "/***** TYPECART PRELUDE START *****/\n"
                  + p.meta.prelude
                  + "\n/***** TYPECART PRELUDE END *****/"
              else
                  "\n"
            + this.declsGeneral (p.decls, pctx, false)

        member this.tpvar (inDecl: bool) (inGhostMethod: bool) (a: TypeArg) =
            // Only print out variance type info for declaration-level printing.
            // variance: prefixes ""/"+"/"-"/"*"/"!"
            // equality: suffix "(==)" for equality types
            // non-heap based: suffix "(!new)"
            let (n, (v, e, h)) = a
            let eS = if e then "(==)" else ""
            let hS = if h then "(!new)" else ""

            if inDecl then
                v + n + eS + hS
            elif inGhostMethod then
                n + hS
            else
                n + eS + hS
        // inDecl should only be set to true when printing out class or datatype declarations.
        // These are the only places when variance type signature should be print out.
        member this.tpvars (inDecl: bool) (inGhostMethod: bool) (ns: TypeArg list) =
            if ns.IsEmpty then
                ""
            else
                "<"
                + listToString (List.map (this.tpvar inDecl inGhostMethod) ns, ", ")
                + ">"

        member this.declsGeneral(ds: Decl list, pctx: Context, braced: Boolean) =
            (if braced then " " else "")
            + indented (listToString (List.map (fun d -> this.decl (d, pctx)) ds, "\n\n"), braced)

        member this.decls(ds: Decl list, pctx: Context) = this.declsGeneral (ds, pctx, true)
        // array dimensions/indices
        member this.dims(ds: Expr list, pctx: Context) = "[" + this.exprsNoBr ds ", " pctx + "]"
        // attributes
        member this.meta(a: Meta) =
            let attr = Map.toList a.attributes
            let attrStr = List.map (fun (k: string, v: string list) -> "{:" + k + (if v.Length = 0 then "" else " " + listToString(v, ", ")) + "} ") attr
            listToString(attrStr, "")

        member this.ghost(g: bool) = if g then "ghost " else ""

        member this.stat(s: bool, ctx: Context) =
            if
                s
                && not (strict && ctx.lookupCurrent().isModule ())
            then
                "static "
            else
                ""

        member this.decl(d: Decl, pctx: Context) =
            let comm =
                d.meta.comment
                |> Option.map (fun s -> "/* " + s + " */\n")
                |> Option.defaultValue ""

            let decls ds = this.decls (ds, pctx.enter (d.name))
            let expr (e: Expr) : string = this.expr e pctx
            
            comm +
            match d with
            | Include _ -> ""
            | Module (n, ds, a) -> "module " + (this.meta a) + n + (decls ds)
            | Datatype (n, tpvs, cons, ds, a) ->
                let consS =
                    List.map (fun x -> this.datatypeConstructor (x, pctx)) cons

                "datatype "
                + (this.meta a)
                + n
                + (this.tpvars true false tpvs)
                + " = "
                + listToString (consS, " | ")
                + (decls ds)
            | Class (n, isTrait, tpvs, p, ds, a) ->
                if isTrait then "trait " else "class "
                + (this.meta a)
                + n
                + (this.tpvars true false tpvs)
                + if p.IsEmpty then
                      ""
                  else
                      (" extends "
                       + listToString (List.map this.classType p, ",")
                       + " ")
                + (decls ds)
            | TypeDef (n, tpvs, sup, predO, isNew, a) ->
                (if isNew then "newtype " else "type ")
                + (this.meta a)
                + n
                + (this.tpvars true false tpvs)
                + " = "
                + (match predO with
                   | Some (x, p, w) ->
                       this.localDecl (LocalDecl(x, sup, false))
                       + " | "
                       + (this.expr p pctx)
                       + (match w with
                          | CompiledZero -> ""
                          | OptOut -> "\n" + indentString + "witness *")
                   | None -> this.tp sup)
            | Field (n, t, eO, g, s, _, a) ->
                this.stat (s, pctx)
                + this.ghost (g)
                + "const "
                + (this.meta a)
                + n
                + ": "
                + (this.tp t)
                + this.exprO (eO, " := ", pctx)
            | Method (methodType, n, tpvs, ins, outs, modifies, reads, decreases, b, g, s, o, a) ->
                let outputsS =
                    match outs.outputType with
                    | Some t -> this.tp t
                    | None -> this.localDeclsBr (outs.decls, true)

                let methodCtx = pctx.enter (n)

                this.stat (s, pctx)
                + (if o then "opaque " else "")
                + (match methodType with
                   | IsLemma
                   | IsLeastLemma
                   | IsGreatestLemma
                   | IsLeastPredicate
                   | IsGreatestPredicate -> ""  // already ghost
                   | _ -> this.ghost (g))
                + methodType.ToString()
                + " "
                + (this.meta a)
                + n
                + (this.tpvars false g tpvs)
                + (this.localDeclsBr (ins.decls, true))
                + (match methodType with
                   | IsLemma
                   | IsPredicate
                   | IsLeastPredicate
                   | IsGreatestPredicate
                   | IsPredicateMethod -> ""
                   | IsMethod -> " returns " + outputsS
                   | _ -> ": " + outputsS)
                + (match modifies with
                   | [] -> ""
                   | _ ->
                       "\n\tmodifies "
                       + (List.map expr modifies |> String.concat ", "))
                + (match reads with
                   | [] -> ""
                   | _ ->
                       "\n\treads "
                       + (List.map expr reads |> String.concat ", "))
                + (match decreases with
                   | [] -> ""
                   | _ ->
                       "\n\tdecreases "
                       + (List.map expr decreases |> String.concat ", "))
                + (this.conditions (true, ins.conditions, methodCtx))
                + (this.conditions (false, outs.conditions, methodCtx))
                + "\n"
                + (match b with
                   | None -> ""
                   | Some e -> (match methodType with
                                | IsLemma
                                | IsMethod -> this.statement e methodCtx
                                | _ -> indentedBraced (this.expr e methodCtx)
                                )
                   )
            | ClassConstructor (n, tpvs, ins, outs, b, a) ->
                "constructor "
                + (this.meta a)
                + if n <> "_ctor" then n else ""
                + (this.tpvars false false tpvs)
                + this.inputSpec (ins, pctx)
                + (this.conditions (false, outs, pctx))
                + "\n"
                + match b with
                  | Some e -> this.statement e pctx
                  | None -> "{}"
            | Import importT -> importT.ToString()
            | Export exportT -> exportT.ToString()
            | DUnimplemented -> UNIMPLEMENTED

        member this.inputSpec(ins: InputSpec, pctx: Context) =
            match ins with
            | InputSpec (lds, rs) ->
                this.localDeclsBr (lds, true)
                + this.conditions (true, rs, pctx)

        member this.outputSpec(outs: OutputSpec, pctx: Context) =
            let r =
                match outs.outputType with
                | Some t -> this.tp t
                | None -> this.localDeclsBr (outs.decls, true)

            r + this.conditions (false, outs.conditions, pctx)

        member this.conditions(require: bool, cs: Condition list, pctx: Context) =
            if cs.IsEmpty then
                ""
            else
                indented (listToString (List.map (fun c -> this.condition (require, c, pctx)) cs, "\n"), false)

        member this.condition(require: bool, c: Condition, pctx: Context) =
            let kw =
                if require then
                    "requires"
                else
                    "ensures"

            kw
            + " "
            + (match snd c with
               | None -> ""
               | Some label -> label + ":")
            + (this.expr (fst c) pctx)

        member this.datatypeConstructor(c: DatatypeConstructor, pctx: Context) =
            c.name + (this.localDeclsBr (c.ins, true))

        member this.tps(ts: Type list) =
            if ts.IsEmpty then
                ""
            else
                "<"
                + listToString (List.map this.tp ts, ",")
                + ">"

        member this.tp(t: Type) = t.ToString()

        member this.exprsNoBr (es: Expr list) (sep: string) (pctx: Context) =
            listToString (List.map (fun e -> this.expr e pctx) es, sep)

        member this.exprs (es: Expr list) (pctx: Context) =
            "(" + (this.exprsNoBr es ", " pctx) + ")"

        member this.exprO(eO: Expr option, sep: string, pctx: Context) : string =
            Option.defaultValue "" (Option.map (fun e -> sep + (this.expr e pctx)) eO)

        member this.noPrintSep(e: Expr) =
            match e with
            | EIf _ // If-stmt without then-block
            | EFor _ // no trailing separator after for body-block
            | EWhile _ -> true
            | _ -> false

        member this.statement (e: Expr) (pctx: Context) =
            let expr e = this.expr e pctx
            let exprsNoBr es sep = this.exprsNoBr es sep pctx

            match e with
            | EBlock es ->
                if es.Length = 0 then
                    "{}"  // empty block
                else
                    let sts =
                        List.map (fun x -> this.statement x pctx) es

                    indentedBraced (String.concat "\n" sts)
            | EBreak l ->
                let label =
                    match l with
                    | Some l -> sprintf " %s" l
                    | None -> ""

                $"break %s{label};"
            (* CalcStmt *)
            (* ExpectStmt *)
            | EQuant (Forall as q, lds, r, b) ->
                "(forall"
                + q.ToString()
                + " "
                + this.localDeclsBr (lds, false)
                + " :: "
                + (match r with
                   | Some e -> expr e + (if q = Forall then " ==> " else " && ")
                   | None -> "")
                + (expr b)
                + ");"
            | EIf (c, t, e) ->
                let elsePart =
                    match e with
                    | None -> "" // avoid using exprO which prints out ";".
                    | Some e -> " else " + this.statement e pctx

                "if "
                + "("
                + (expr c)
                + ") "
                + (this.statement t pctx)
                + elsePart
            | EAlternative(conds, bodies) ->
                let alternativeCase (cond, body) =
                    "case "
                    + (expr cond)
                    + " =>"
                    + (expr body)
                "if " + String.concat "" (List.map alternativeCase (List.zip conds bodies))
            | EMatch (e, t, cases, dfltO) ->
                let defCase =
                    match dfltO with
                    | None -> []
                    | Some e ->
                        [ { vars = []
                            patterns = [ EWildcard ]
                            body = e } ] // case _ => e

                let csS =
                    List.map (fun (c: Case) -> this.caseStatement c pctx) (cases @ defCase)

                "match "
                + (expr e)
                + " "
                + indentedBraced (listToString (csS, "\n"))
            (* ModifyStmt *)
            | EPrint es ->
                "print "
                + (String.concat ", " (List.map expr es))
                + ";"
            | EReturn es -> "return " + (exprsNoBr es ", ") + ";"
            | EReveal es ->
                if es.IsEmpty then
                    "" // happens when unresolved expressions are dropped in DafnyToYIL
                else
                    "reveal "
                    + (String.concat ", " (List.map expr es))
                    + ";"
            | EUpdate (ns, u) ->
                let lhsExprs = List.map expr ns

                listToString (lhsExprs, ",")
                + (this.update u pctx)
                + ";"
            | EVar _ -> expr e + ";"
            | EMemberRef (r, m, _) -> this.receiver (r, pctx) + m.name + ";"
            | EWhile (c, e, l) ->
                let label =
                    match l with
                    | Some l -> sprintf "%s: " l
                    | None -> ""

                sprintf "%s while (%s) %s" label (expr c) (this.statement e pctx)
            | EFor (index, init, last, up, body) ->
                let d = EDecls([index], [ EVar index.name ], [ plainUpdate init ])

                let forInitCtx = pctx.setPos (InForLoopInitializer)
                let forBodyCtx = pctx.setPos (InForLoopBody)

                "for "
                + this.expr d forInitCtx
                + (if up then " to " else " downto ")
                + (expr last)
                + " "
                + this.statement body forBodyCtx
            | ELet (v, ex, orfail, lhs, d, e) ->
                "var "
                + (exprsNoBr lhs ", ")
                + (match (ex, orfail) with
                   | true, false -> " := "
                   | true, true -> " :- "
                   | false, false -> " :| "
                   | _ -> failwith "unsupported let expression")
                + (exprsNoBr d ", ")
                + "; "
                + (this.statement e pctx)
            | EAssert (e, p) ->
                "assert "
                + (expr e)
                + (match p with
                   | None -> ";"
                   | Some proof -> " by " + (this.statement proof pctx))
            | EAssume _
            | EExpect _
            | EDecls _
            | EAnonApply _
            | EMethodApply _
            | EDeclChoice _ as e -> (expr e) + ";"
            | ECommented (c, e) -> "/* " + c + " */" + this.statement e pctx
            | EUnimplemented -> "/* UNIMPLEMENTED */"
            | b ->
                failwith "encountered non-statement in statement: "
                + (b.ToString())


        member this.expr (e: Expr) (pctx: Context) : string =
            this.exprWithPrecedence e 0 pctx
        
        member this.exprWithPrecedence (e: Expr) (precedence: int) (pctx: Context) : string =
            // We need to add parentheses to the result if the operator precedence is strictly lower than |precedence|.
            // For example, if |precedence| == 6 ("+"), we do not need to add parentheses if we encounter "*" or "+",
            // but we need to add parentheses if we encounter "<" (with precedence 4).
            //
            // expr 0 e: no need to add parentheses
            // expr 11 e: add parentheses unless it's a primary expression, e.g., EVar
            let expr p e = this.exprWithPrecedence e p pctx
            let exprs es = this.exprs es pctx
            let exprO e sep = this.exprO (e, sep, pctx)
            let exprsNoBr es sep = this.exprsNoBr es sep pctx

            let dims ds = this.dims (ds, pctx)
            let receiver r = match r with
                                | StaticReceiver s ->
                                    if s.path.isAncestorOf(pctx.pathWithoutPseudoModule()) then
                                        ""
                                    else
                                        this.receiver (r, pctx)
                                | ObjectReceiver _ -> this.receiver (r, pctx)
            let case c = this.case c pctx
            let tp = this.tp
            let tps = this.tps

            match e with
            | EVar n ->
                let n1 = n.Replace("_mcc#", "mcc_") // Dafny-generated names that are not valid Dafny concrete syntax
                let n2 = if n1.StartsWith("_") then "_" else n1 // Dafny-generated anonymous variables
                let n3 = n2.Replace("#", "x") // Variables with no names
                n3
            | EThis -> "this"
            | ENew (ct, args) -> "new " + this.classType (ct) + (exprs args)
            | ENull _ -> "null"
            | EMemberRef (r, m, _) -> (receiver r) + m.name
            | EBool (v) ->
                match v with
                | true -> "true"
                | false -> "false"
            | EChar (v) -> "'" + v.ToString() + "'"
            | EString (v) -> "\"" + v.ToString() + "\""
            // EToString compile from sequence display expressions of char sequences
            | EToString es -> "[" + (exprsNoBr es ", ") + "]"
            | EInt (v, _) -> v.ToString()
            | EReal (v, _) -> v.ToDecimalString()
            | EQuant (q, lds, r, b) ->
                (if 0 < precedence then "(" else "")
                + q.ToString()
                + " "
                + this.localDeclsBr (lds, false)
                + " :: "
                + (match r with
                   // ==> is 2
                   // && is 3
                   | Some e -> (if q = Forall then expr 3 e + " ==> " + expr 3 b else expr 4 e + " && " + expr 4 b)
                   | None -> expr 0 b)
                + (if 0 < precedence then ")" else "")
            | EOld e -> "old(" + (expr 0 e) + ")"
            | ETuple (es) -> exprs es
            | EProj (e, i) -> expr 11 e + "." + i.ToString()
            | EFun (vs, cond, _, e) ->
                (if 0 < precedence then "(" else "")
                + (this.localDeclsBr (vs, true))
                + (Option.defaultValue "" (Option.map (fun c -> " " + this.condition(true, c, pctx)) cond))
                + " => "
                + (expr 0 e)
                + (if 0 < precedence then ")" else "")
            | ESet (_, es) -> "{" + (exprsNoBr es ", ") + "}"
            | ESetComp (lds, predicate, body) ->
                let ldsStr =
                    List.map this.localDecl lds |> String.concat ", "

                "set "
                + ldsStr
                + " | "
                + (expr 0 predicate)
                + " :: "
                + (expr 0 body)
            | ESeq (_, es) -> "[" + (exprsNoBr es ", ") + "]"
            | ESeqConstr (_, l, i) -> "seq(" + (expr 0 l) + ", " + (expr 0 i) + ")"
            | ESeqSelect (s, _, elem, f, t) ->
                if elem then
                    (expr 11 s) + "[" + (expr 0 (Option.get f)) + "]"
                else
                    (expr 11 s)
                    + "["
                    + exprO f ""
                    + ".."
                    + exprO t ""
                    + "]"
            | ESeqUpdate (s, i, e) -> (expr 11 s) + "[" + (expr 11 i) + " := " + (expr 0 e) + "]"
            | EArray (t, d, i) -> "new " + t.ToString() + dims (d) + this.arrayInitializer(i, pctx)
            | EMultiSelect (a, i) -> (expr 11 a) + dims (i)
            | EArrayUpdate (a, i, e) -> (expr 11 a) + dims (i) + " := " + (expr 0 e)
            | EMapKeys (e) -> (expr 11 e) + ".Keys"
            | EMapValues (e) -> (expr 11 e) + ".Values"
            | EMapDisplay (elts) ->
                let str =
                    List.fold (fun l (k, v) -> (String.concat " := " [ expr 0 k; expr 0 v ]) :: l) [] elts

                let str = String.concat " , " str
                "map [" + str + "]"
            | EMapComp (lds, p, tL, tR) ->
                let ldsStr =
                    List.map this.localDecl lds |> String.concat ", "

                "map "
                + ldsStr
                + " | "
                + (expr 0 p)
                + " :: "
                + match tL with
                  | None -> expr 0 tR
                  | Some tL -> (expr 11 tL) + " := " + (expr 0 tR)
            | EUnOpApply (op, e) -> this.unaryOperator op precedence (expr (this.unaryOperatorPrecedence op) e)
            | EBinOpApply (op, e1, e2) ->
                let resolvedOp = this.binaryOperatorResolve op
                this.binaryOperator resolvedOp precedence (expr (this.binaryOperatorPrecedenceLeft resolvedOp) e1)
                    (expr (this.binaryOperatorPrecedenceRight resolvedOp) e2)
            | EAnonApply (f, es) -> (expr 11 f) + (exprs es)
            | EMethodApply (r, m, ts, es, _) -> (receiver r) + m.name + (exprs es)
            | EConstructorApply (c, ts, es) ->
                let cS =
                    if pctx.pos = PatternPosition then
                        c.name
                    else
                        c.ToString()

                cS + (exprs es)
            | EBlock es ->
                // throw out empty blocks; these are usually artifacts of the processing
                let notEmptyBlock e =
                    match e with
                    | EBlock []
                    | ECommented (_, EBlock []) -> false
                    | _ -> true
                let esNonEmpty = List.filter notEmptyBlock es
                if esNonEmpty.IsEmpty then
                    ""
                else
                    // statement 0, statement 1, ..., statement n-2, expr n-1
                    let sts = List.map (fun x -> this.statement x pctx) esNonEmpty[..esNonEmpty.Length - 2]
                    let esS = String.concat "\n" (sts @ [ expr 0 (esNonEmpty.Item(esNonEmpty.Length - 1)) ])
                    // no braces - Dafny parses them as sets
                    "\n" + esS
            | ELet (v, x, orfail, lhs, d, e) ->
                "var "
                + (exprsNoBr lhs ", ")
                + (match (x, orfail) with
                   | true, false -> " := "
                   | true, true -> " :- "
                   | false, false -> " :| "
                   | _ -> failwith "unsupported let expression")
                + (exprsNoBr d ", ")
                + "; "
                + (expr 0 e)
            | EIf (c, t, e) ->
                let elsePart =
                    match e with
                    | None -> "" // avoid using exprO which prints out ";".
                    | Some e -> " else " + expr 0 e

                let s =
                    "if " + (expr 0 c) + " then " + (expr 0 t) + elsePart

                (if 0 < precedence then "(" else "")
                + s
                + (if 0 < precedence then ")" else "")
            | EAlternative (conds, bodies) ->
                let alternativeCase (cond, body) =
                    "case "
                    + (expr 0 cond)
                    + " =>"
                    + (expr 0 body)
                "if " + String.concat "" (List.map alternativeCase (List.zip conds bodies))
            | EFor (index, init, last, up, body) ->
                let d = EDecls([ index ], [ EVar index.name ], [ plainUpdate init ])

                let forInitCtx = pctx.setPos (InForLoopInitializer)
                let forBodyCtx = pctx.setPos (InForLoopBody)

                "for "
                + this.expr d forInitCtx
                + (if up then " to " else " downto ")
                + (expr 0 last)
                + " "
                + this.expr body forBodyCtx
            | EWhile (c, e, l) ->
                let label =
                    match l with
                    | Some l -> sprintf "%s: " l
                    | None -> ""

                sprintf "%swhile (%s)%s" label (expr 0 c) (expr 0 e)
            | EReturn (es) -> (exprsNoBr es ", ")
            | EBreak l ->
                let label =
                    match l with
                    | Some l -> sprintf " %s" l
                    | None -> ""

                sprintf "break %s" label
            | EMatch (e, t, cases, dfltO) ->
                let defCase =
                    match dfltO with
                    | None -> []
                    | Some e ->
                        [ { vars = []
                            patterns = [ EWildcard ]
                            body = e } ] // case _ => e

                let csS =
                    List.map (fun (c: Case) -> case c) (cases @ defCase)

                "match "
                + (expr 0 e)
                + " "
                + indentedBraced (listToString (csS, "\n"))
            | EDecls (vars, lhs, rhs) ->
                let varQual =
                    if pctx.pos = InForLoopInitializer then
                        ""
                    else
                        "var "
                
                varQual
                + (exprsNoBr lhs ", ")
                + (this.updates rhs pctx)
            | EUpdate (ns, u) ->
                let lhsExprs = List.map (expr 0) ns

                listToString (lhsExprs, ",")
                + (this.update u pctx)
            | EDeclChoice (ld, e) -> "var " + (this.localDecl ld) + " :| " + (expr 0 e)
            | ETypeConversion (e, t) ->
                (if 9 < precedence then "(" else "")
                + (expr 9 e)
                + " as "
                + (tp t)
                + (if 9 < precedence then ")" else "")
            | ETypeTest (e, t) ->
                (if 9 < precedence then "(" else "")
                + (expr 9 e)
                + " is "
                + (tp t)
                + (if 9 < precedence then ")" else "")
            | EPrint es -> "print " + (String.concat ", " (List.map (expr 0) es))
            | EAssert (e, p) ->
                "assert "
                + (expr 0 e)
                + (match p with
                   | None -> ""
                   | Some proof -> " by " + (this.statement proof pctx))
            | EAssume e -> "assume " + (expr 0 e)
            | EExpect e -> "expect " + (expr 0 e)
            | EReveal es ->
                if es.IsEmpty then
                    "reveal true" // empty reveal not allowed in Dafny
                else
                    "reveal "
                    + (String.concat ", " (List.map (expr 0) es))
            | ECommented (s, e) -> "/* " + s + " */ " + expr 0 e
            | EUnimplemented -> UNIMPLEMENTED

        member this.binaryOperatorResolve (op: string): string =
            // reconstruct dafny Opcode by converting string back to enum.
            let mutable eOp = BinaryExpr.ResolvedOpcode.YetUndetermined
            if Enum.TryParse<BinaryExpr.ResolvedOpcode>(op, &eOp) then
                (eOp
                   |> BinaryExpr.ResolvedOp2SyntacticOp
                   |> BinaryExpr.OpcodeString)
            else
                failwith $"unsupported binary operator %s{op}"

        member this.binaryOperator (op: string) (precedence: int) (eSL: string) (eSR: string) : string =
            (if this.binaryOperatorPrecedence op < precedence then "(" else "")
            + eSL
            + " "
            + op
            + " "
            + eSR
            + (if this.binaryOperatorPrecedence op < precedence then ")" else "")

        member this.binaryOperatorPrecedence (op: string) =
            match op with
            | "<==>" -> 1
            | "==>"
            | "<==" -> 2
            | "&&"
            | "||" -> 3
            | "=="
            | "!="
            | "<"
            | "<="
            | ">="
            | ">"
            | "!!"
            | "in"
            | "!in" -> 4
            | "<<"
            | ">>" -> 5
            | "+"
            | "-" -> 6
            | "*"
            | "/"
            | "%" -> 7
            | "&"
            | "|"
            | "^" -> 8
            | _ -> failwith $"unsupported binary operator %s{op}"

        member this.binaryOperatorPrecedenceLeft (op: string) =
            match this.binaryOperatorPrecedence op with
            | 1 -> 1
            | 2 -> 3  // avoid "a ==> b <== c"
            | 3 -> 4  // force parentheses around && and ||
            | 4 -> 5  // comparison chains are already desugared
            | 5 -> 5
            | 6 -> 6
            | 7 -> 7
            | 8 -> 9  // force parentheses around &, | and ^
            | _ -> 0

        member this.binaryOperatorPrecedenceRight (op: string) =
            match op with
            // associative operator
            | "<==>" -> this.binaryOperatorPrecedence op
            | _ -> this.binaryOperatorPrecedence op + 1

        // For reference, see unary expression handling in dafny Printer.cs file.
        // Unary minus is handled as a binary minus so it does not appear here.
        member this.unaryOperator (op: string) (precedence: int) (eS: string) =
            match op with
            | "Not" ->
                (if 10 < precedence then "(" else "")
                + "!"
                + eS
                + (if 10 < precedence then ")" else "")
            | "Cardinality" -> "|" + eS + "|"
            | "Fresh" -> "fresh(" + eS + ")"
            | "Allocated" -> "allocated(" + eS + ")"
            | "Lit" -> "Lit(" + eS + ")"
            | _ -> failwith $"unsupported unary operator %s{op}"

        member this.unaryOperatorPrecedence (op: string) =
            match op with
            | "Not" -> 10
            | _ -> 0

        member this.localDeclsBr(lds: LocalDecl list, brackets: bool) =
            (if brackets then "(" else "")
            + listToString (List.map this.localDecl lds, ", ")
            + (if brackets then ")" else "")

        member this.localDecls(lds: LocalDecl list) = this.localDeclsBr (lds, lds.Length <> 1)

        member this.update (u: UpdateRHS) (pctx: Context) =
            let op = if u.monadic.IsSome then ":-" else ":="
            " " + op + " " + (this.expr u.df pctx)

        member this.updates (u: UpdateRHS list) (pctx: Context) =
            if u.Length = 0 then
                ""
            else
                let monadicList = List.map (fun (x: UpdateRHS) -> x.monadic) u
                let monadic = if List.forall (fun (x: Type option) -> x.IsNone) monadicList then
                                  None
                              elif List.forall (fun (x: Type option) -> x.IsSome) monadicList then
                                  Some(TTuple (List.map (fun (x: Type option) -> x.Value) monadicList))
                              else
                                  error "RHS must be either all monadic or all non-monadic"
                let op = if monadic.IsSome then ":-" else ":="
                
                let rhsExprs = List.map (fun (x: UpdateRHS) -> x.df) u
                " " + op + " " + (this.exprsNoBr rhsExprs ", " pctx)

        member this.localDecl(ld: LocalDecl) =
            if ld.name.StartsWith('#') then
                (this.tp ld.tp)  // no name, only type
            else
                ld.name + ": " + (this.tp ld.tp)

        member this.classType(ct: ClassType) =
            ct.path.ToString() + (this.tps ct.tpargs)
        
        member this.arrayInitializer(init: ArrayInitializer, pctx: Context) =
            match init with
            | Uninitialized -> ""
            | ValueList es -> this.dims(es, pctx)
            | ComprehensionLambda e -> "(" + (this.expr e pctx) + ")"

        member this.receiver(rcv: Receiver, pctx: Context) =
            // do not print out the "." separator if receiver is empty.
            let dot s =
                match s with
                | "" -> ""
                | _ -> s + "."

            match rcv with
            | StaticReceiver (ct) -> this.classType (ct) |> dot // ClassType --> path, tpargs
            | ObjectReceiver (e) -> this.expr e pctx |> dot

        member this.caseStatement (case: Case) (pctx: Context) =
            // Remove the extra braces
            let bodyStr = match case.body with
                          | EBlock es -> String.concat "\n" (List.map (fun x -> this.statement x pctx) es)
                          | _ -> this.statement case.body pctx

            "case "
            + this.exprsNoBr case.patterns " | " (pctx.setPos PatternPosition)
            + " => "
            + indented (bodyStr, false)

        member this.case (case: Case) (pctx: Context) =
            "case "
            + this.exprsNoBr case.patterns " | " (pctx.setPos PatternPosition)
            + " => "
            + indented (this.expr case.body pctx, false)

    /// shortcut to create a fresh strict printer
    let printer () = Printer(true)
