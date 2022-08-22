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
    [<CustomEquality;NoComparison>]
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
        member this.prefix(s: string) = match this with Path ps -> Path (s :: ps)
        member this.append(ns: Path) =
            Path(
                this.names
                @ List.filter (fun x -> x <> "") ns.names
            )
        member this.parent = Path(listDropLast (this.names))
        member this.name = listLast (this.names)
        member this.namesWithoutLast() =
            match List.rev this.names with
            | _ :: t -> List.rev t
            | [] -> []
        member this.transformLast(name': string) =
            match List.rev this.names with
            | [] -> failwith "cannot transform last of an empty path"
            | _ :: t -> name' :: t
            |> List.rev
            |> Path
        /// this is prefix of that (reflexive)
        member this.isAncestorOf(p: Path) =
            let l = this.names.Length
            p.names.Length >= l
            && p.names.[..l - 1] = this.names

        override this.ToString() = listToString (this.names, ".")
        
        // Two paths is equal if every pair of elements in each position are equal.
        override this.Equals(that: Object) =
            let eq (that: Path) =
                match this, that with
                | Path (a :: t), Path (b :: t') -> a.Equals(b) && (Path t).Equals(Path t')
                | Path [], Path [] -> true
                | _ -> false
            match that with
            | :? Path as that -> eq that
            | _ -> false
        
        override this.GetHashCode() =
            match this with Path ps -> (String.concat ";" ps).GetHashCode()
            
        
    // meta-information
    [<CustomEquality;NoComparison>]
    type Meta =
        { comment: string option; position: Position option; prelude: string }
        override this.GetHashCode() = 0
        // we make all Meta objects equal so that they are ignored during diffing
        override this.Equals(that: Object) =
            match that with
            | :? Meta -> true
            | _ -> false
    // position in a source file, essentially the same as Microsoft.Boogie.IToken
    and Position =
        { filename: String
          pos: int
          line: int
          col: int }
        override this.ToString() =
            $"{this.filename}@{this.line.ToString()}:{this.col.ToString()}"

    // ***** auxiliary methods
    let emptyMeta = { comment = None; position = None; prelude = "" }

    /// name of nonymous variables
    let anonymous = "_"
    
    /// Three Dafny method types. This is going to matter when pretty-printing, since
    /// Dafny distinguishes the set of syntaxes allowed when printing different methods.
    type MethodTypePayload =
        | IsMethod
        | IsFunctionMethod
        | IsFunction
        | IsLemma
        | IsPredicate
        | IsPredicateMethod
        member this.isGhost() =
            match this with
            | IsMethod | IsFunctionMethod | IsPredicateMethod -> false
            | IsFunction | IsLemma | IsPredicate -> true
        
        override this.ToString() =
            match this with
            | IsMethod -> "method"
            | IsFunctionMethod -> "function method"
            | IsPredicateMethod -> "predicate method"
            | IsFunction -> "function"
            | IsLemma -> "lemma"
            | IsPredicate -> "predicate"
    
    type MethodType =
        | NonStaticMethod of m: MethodTypePayload
        | StaticMethod of m: MethodTypePayload
        member this.map() =
            match this with
            | NonStaticMethod m | StaticMethod m -> m
    
    type ExportType(provides: Path list, reveals: Path list) =
        new() = ExportType([], [])
        member this.provides = provides
        member this.reveals = reveals
        override this.ToString() =
            let lts (ps: Path list) = (listToString(ps |> List.map (fun p -> p.name), ", "))
            "export \n"
                + "   provides " + (lts this.provides)
                + "\n"
                + "   reveals " + (lts this.reveals)
        
        
        override this.Equals(that) =
            match that with
            | :? ExportType as that ->
                this.provides.Equals(that.provides) && this.reveals.Equals(that.reveals)
            | _ -> false
    
        override this.GetHashCode() = this.ToString().GetHashCode()
    
    type ImportType =
        | ImportDefault of Path
        | ImportOpened of Path
        | ImportEquals of lhsDir: Path * rhsDir: Path
        override this.ToString() =
            match this with
            | ImportDefault p -> "import " + p.ToString()
            | ImportOpened p -> "import opened " + p.ToString()
            | ImportEquals (lhs, rhs) -> "import " + lhs.ToString() + " = " + rhs.ToString()
        // for ImportEquals, compare rhsDir since it is the given name to the import.
        member this.pathEquals(p': Path) =
            match this with
            | ImportDefault p
            | ImportOpened p
            | ImportEquals (_, p) -> p.Equals(p')
        // return path of import. For ImportEquals, return path of rhs
        member this.getPath() =
            match this with
            | ImportDefault p
            | ImportOpened p
            | ImportEquals (_, p) -> p
        member this.prefix(pre: string) =
            match this with
            | ImportDefault p -> ImportDefault (p.prefix(pre))
            | ImportOpened p -> ImportOpened (p.prefix(pre))
            | ImportEquals (lhs, p) -> ImportEquals (lhs, p.prefix(pre))
        
    
    (* toplevel declaration
       The program name corresponds to the package name or root namespace.

       This could be a special case of Decl or even just a Module.
       But for now we keep it separate because:
       - Modules aren't nested for now, and we want to forbid that altogether.
       - We way want to add information here later.
       - It is convenient to have a type of programs and not just a constructor.
    *)
    type Program = { name: string; decls: Decl list; meta: Meta }

    (* declarations
       Modules and datatypes are child-bearing, i.e., can contain nested declarations.
       Each declaration is named uniquely within its parent.
       Within the program each declaration is uniquely identified.
    *)
    and Decl =
        (* Include "..." is a preprocessor-like intrinsic in dafny that causes dafny to inline the file specified.
           We need to include it here essentially because translations.dfy can also use types from joint.dfy. *)
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
        | ClassConstructor of name: string * tpvars: TypeArg list * ins: InputSpec * outs: Condition list * body: Expr option * meta: Meta
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
            methodIs: MethodType *
            name: string *
            tpvars: TypeArg list *
            ins: InputSpec *
            out: OutputSpec *
            body: Expr option *
            ghost: bool *
            isStatic: bool *
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
            | Method (_, _, _, _, _, _, _, _, meta) -> meta
            | Field (_, _, _, _, _, _, meta) -> meta
            | TypeDef (_, _, _, _, _, meta) -> meta
            | _ -> emptyMeta

        member this.name =
            match this with
            | Module (n, _, _) -> n
            | Datatype (n, _, _, _, _) -> n
            | Class (n, _, _, _, _, _) -> n
            | ClassConstructor (n, _, _, _, _, _) -> n
            | Method (_, n, _, _, _, _, _, _, _) -> n
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
            | Method (_, _, tpvs, _, _, _, _, _, _) -> tpvs
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
        member this.filterChildren (mustPreserve: Decl -> bool) =
            let f ds = List.filter (mustPreserve) ds
            match this with
            | Module (x, ds, y) -> [ Module (x, f ds, y) ]
            | Datatype (a, b, c, ds, d) -> [ Datatype (a, b, c, ds, d) ]
            | Class (a, b, c, d, ds, e) -> [ Class (a, b, c, d, ds, e) ]
            | _ -> []
    and TypeArg = string * (bool option)  // true/false for co/contravariant
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
        | TArray of Bound * Type // array of any dimensions
        | TObject // supertype of all classes
        | TNullable of Type
        // identifiers
        | TApply of op: Path * args: Type list
        | TApplyPrimitive of op: Path * underlyingType: Type
        | TVar of string
        // dummy for missing cases
        | TUnimplemented
        override this.ToString() =
            let tps(ts: Type list) =
                if ts.IsEmpty then "" else "<" + listToString (ts, ",") + ">"
            let product(ts: Type list) =
                if ts.Length = 1 then ts.Head.ToString() else "(" + listToString (ts, ",") + ")"

            match this with
            | TUnit -> "unit"
            | TBool -> "bool"
            | TInt b -> "int" + b.ToString()
            | TNat b -> "nat" + b.ToString()
            | TChar -> "char"
            | TString b -> "string" + b.ToString()
            | TReal b -> match b with | Bound (Some 32) -> "float" | Bound (Some 64) -> "double" | _ -> "real"
            | TBitVector (w) -> "bv" + w.ToString()
            | TVar (n) -> n
            | TApply (op, args) -> (String.concat "." op.names) + (tps args)
            | TApplyPrimitive (op, t) ->
                match t with
                | TApply _ -> t.ToString()
                | _ ->
                    let pathUntil = op.namesWithoutLast()
                    match pathUntil with
                    | [] -> t.ToString()
                    | _ -> (String.concat "." pathUntil) + "." + (t.ToString())
            | TTuple (ts) -> product ts
            | TFun (ins, out) -> (product ins) + "->" + (out.ToString())
            | TSeq (b,t) -> "seq" + b.ToString() + (tps [ t ])
            | TSet (b,t) -> "set" + b.ToString() + (tps [ t ])
            | TArray (b,t) -> "arr" + b.ToString() + (tps [ t ])
            | TMap (b, d, r) -> "map" + b.ToString() + (tps [ d; r ])
            | TObject -> "object"
            | TNullable t -> t.ToString() + "?"
            | TUnimplemented -> "UNIMPLEMENTED"

    // for size-limited version of types defined in Yucca's TypeUtil, gives the size in bits
    // See DafnyToYIL for the possibly bound values, usually 32 or 64
    and Bound =
      | Bound of int option
      override this.ToString() = match this with | Bound (Some i) -> i.ToString() | Bound None -> ""
    
    (* typed variable declaration used in method input/output, binders, and local variables declararations
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
    and Case = { vars: LocalDecl list; pattern: Expr; body: Expr }

    /// input specification: typed variables and preconditions
    and InputSpec =
       | InputSpec of LocalDecl list * Condition list
       member this.decls = match this with InputSpec(ds,_) -> ds
       member this.conditions = match this with InputSpec(_,cs) -> cs

    /// output specification: typed variables and postconditions
    // to avoid case distinctions, the case of an unnamed output type is represented as a single anonymous variable
    and OutputSpec =
        | OutputSpec of LocalDecl list * Condition list
        member this.decls = match this with | OutputSpec (ds, _) -> ds
        /// the unnamed output type if any
        member this.outputType =
            match this.decls with
            | [ld] when ld.isAnonymous() -> Some ld.tp
            | _ -> None
        /// the output declarations (i.e., without the dummy declaration for an output type)
        member this.namedDecls = this.decls |> List.filter (fun ld -> not (ld.isAnonymous())) 
        member this.conditions = match this with | OutputSpec (_, cs) -> cs

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
        | EOld of Expr // used in ensures conditions of methods in classes to refer to previous state
        | ETuple of elems: Expr list
        | EProj of tuple: Expr * index: int
        | EFun of vars: LocalDecl list * out: Type * body: Expr
        // *** introduction/elimination forms for built-in type operators
        | ESet of tp: Type * elems: Expr list
        | ESetComp of lds: LocalDecl list * p: Expr // set comprehension. {x in lds | p(lds)}
        | ESeq of tp: Type * elems: Expr list
        | ESeqConstr of tp: Type * length: Expr * init: Expr // builds sequence init(0), ..., init(length-1)
        | EMapAt of mp: Expr * arg: Expr
        | EMapKeys of map: Expr
        | EMapDisplay of map : (Expr * Expr) list // explicit map represented as a list
        // map comprehension where tL is an expression over the preimage and tR is an expression mapping preimage to
        // image. If tL = Some tLF, generates the map tLF(p(lds)) -> tR(p(lds)). Otherwise, generates the map
        // p(lds) -> tR(p(lds)).
        | EMapComp of lds : LocalDecl list * p : Expr * tL : Expr Option * tR : Expr
        | ESeqAt of seq: Expr * index: Expr
        | ESeqRange of seq: Expr * beginIndex: Expr option * endIndex: Expr option
        | ESeqUpdate of seq: Expr * index: Expr * df: Expr
        | EArrayAt of array: Expr * index: Expr list
        | EArrayRange of array: Expr * beginIndex : Expr option * endIndex: Expr option
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
        | EAssert of Expr
        | EAssume of Expr
        | EReveal of Expr list // dafny `reveal ... ;` statement
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
        new() = ModuleImports(Path[], [])
        member this.modulePath = modulePath
        member this.imports = imports
        member this.setModulePath(modulePath: Path) = ModuleImports(modulePath, this.imports)
        member this.addImport(importPath: Path, importType: ImportType) =
            ModuleImports(this.modulePath, importType :: this.imports)
    
    // auxiliary methods
    
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
    let block(b: Expr): Expr =
        match b with
        | EBlock _ -> b
        | _ -> EBlock [b]
    
    /// invariant type argument given by name
    let plainTypeArg n = (n,None)
    
    /// the corresponding list of TVars
    let typeargsToTVars (tvs: TypeArg list) = List.map (fun (n,_) -> TVar n) tvs
    
    let NoBound = Bound None
    let Bound8 = Bound (Some 8)
    let Bound16 = Bound (Some 16)
    let Bound32 = Bound (Some 32)
    let Bound64 = Bound (Some 64)
    /// Some Java-specific types.
    let Bound31 = Bound (Some 31)
    let Bound63 = Bound (Some 63)
    
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

    // Is a given path an anonymous Dafny tuple contructor
    let isDafnyTuple (p: Path) = p.name.StartsWith("_#Make")
    
    /// OutputSpec with a plain return type
    let outputType(t: Type, cs: Condition list) = OutputSpec([LocalDecl(anonymous, t, false)], cs)
    
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
        let pat = if isDafnyTuple(c) then ETuple(lts) else EConstructorApply(c, [], lts)
        { vars = lds; pattern = pat; body = bd }
   
    // local variables introduced by an expression (relevant when extending the context during traversal)
    // also defines which variables are visible to later statements in the same block
    let exprDecl (e: Expr) : LocalDecl list =
        match e with
        | EDecls ds -> List.map (fun (x, _) -> x) ds
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
            let selectors = List.collect (fun (c: DatatypeConstructor) -> c.ins) cs
            let testers = List.map (fun (c: DatatypeConstructor) -> LocalDecl(testerName c.name, TBool, false)) cs
            List.map mkField (List.append (List.distinct selectors) testers)
        | Module(_, decls, _) -> List.collect implicitChildren decls
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
            let children = parentDecl.children

            match List.tryFind (fun (x: Decl) -> x.name = path.name) children with
            | Some d -> d
            | None ->
                let implChildren = (implicitChildren parentDecl)

                match List.tryFind (fun (x: Decl) -> x.name = path.name) implChildren with
                | Some (d) -> d
                | None -> error $"Path [{path}] not valid in {prog.name}"
    (* as above, but returns a constructor *)
    let lookupConstructor (prog: Program, path: Path) : DatatypeConstructor =
        match lookupByPath (prog, path.parent) with
        | Datatype (_, _, ctrs, _, _) -> List.find (fun c -> c.name = path.name) ctrs
        | _ -> error $"parent not a datatype: {path}"

    
    /// A trait for contextual information required during printing.
    type PrintingContext =
        abstract member enterMethod: (string * MethodType) -> PrintingContext
        abstract member enterForLoopInitializer: unit -> PrintingContext
        abstract member enterForLoopBody: unit -> PrintingContext
        abstract member leaveForLoopBody: unit -> PrintingContext
        abstract member inMethod: unit -> (string * MethodType) option 
        abstract member inForLoopInitializer: unit -> bool
        abstract member inForLoopBody: unit -> bool
        
    /// Trivial implementation of PrintingContext.
    type EmptyPrintingContext() =    
        interface PrintingContext with
            member this.enterMethod(_) = EmptyPrintingContext()
            member this.enterForLoopInitializer() = EmptyPrintingContext()
            member this.enterForLoopBody() = EmptyPrintingContext()
            member this.leaveForLoopBody() = EmptyPrintingContext()
            member this.inMethod() = None
            member this.inForLoopInitializer() = false
            member this.inForLoopBody() = false
            
    
    /// used in Context to track where we are
    /// adjust this if we ever need to track if we are in the final position of an expression
    type ContextPosition = BodyPosition | OtherPosition
    (* ***** contexts: built during traversal and used for lookup of iCodeIdentifiers

       A Context stores an entire program plus information about where we are during its traversal:
       - prog: the program
       - currentDecl: path to the declarations into which we have traversed, e.g.,
         []: toplevel of program
         ["m", "d"]: in datatype d in module m
       - tpvars: type parameters of enclosing declarations (inner most last)
       - vars: local variables that have been declared (most recent last)
       - pos: tracks if we are in the body of a method
       - modulePath: the path of the current module
       - 

       invariant: currentDecl is always a valid path in prog, i.e., lookupByPath succeeds for every prefix
       
       TODO: remove importPaths and just use the tree representation of imports.
    *)
    type Context(prog: Program, currentDecl: Path, tpvars: TypeArg list, vars: LocalDecl list, pos: ContextPosition,
                 modulePath: Path, importPaths: ImportType list, currMethod: (string * MethodType) option, inForLoopInitializer: bool, inForLoopBody: bool) =
        // convenience constructor and accessor methods
        new(p: Program) = Context(p, Path([]), [], [], OtherPosition, Path[], [], None, false, false)
        
        // A program context can be supplied to the printer.
        interface PrintingContext with
            member this.enterMethod(m) = Context(prog, currentDecl, tpvars, vars, pos, modulePath, importPaths, Some m, inForLoopInitializer, inForLoopBody)
            member this.enterForLoopInitializer() = Context(prog, currentDecl, tpvars, vars, pos, modulePath, importPaths, currMethod, true, inForLoopBody)
            member this.enterForLoopBody() = Context(prog, currentDecl, tpvars, vars, pos, modulePath, importPaths, currMethod, inForLoopInitializer, true)
            member this.leaveForLoopBody() = Context(prog, currentDecl, tpvars, vars, pos, modulePath, importPaths, currMethod, inForLoopInitializer, false)
            member this.inMethod() = this.currMethod
            member this.inForLoopInitializer() = this.inForLoop
            member this.inForLoopBody() = this.inForLoopBody
        
        member this.prog = prog
        member this.currentDecl = currentDecl
        member this.tpvars = tpvars
        member this.vars = vars
        member this.lookupCurrent() = lookupByPath (prog, currentDecl)
        member this.pos = pos
        member this.modulePath = modulePath
        member this.importPaths = importPaths
        member this.currMethod = currMethod
        member this.inForLoop = inForLoopInitializer
        member this.inForLoopBody = inForLoopBody

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

        member this.currentMeta() =
            this.lookupCurrent().meta
        
        /// convenience method for creating a new context when traversing into a child declaration
        member this.enter(n: string) : Context =
            Context(prog, currentDecl.child (n), tpvars, vars, pos, modulePath, importPaths, currMethod, inForLoopInitializer, inForLoopBody)
        /// convenience method for adding type variable declarations to the context
        member this.addTpvars(ns: string list) : Context =
            Context(prog, currentDecl, List.append tpvars (List.map plainTypeArg ns), vars, pos, modulePath, importPaths, currMethod, inForLoopInitializer, inForLoopBody)
        /// convenience method for adding type variable declarations to the context
        member this.addTpvars(tvs: TypeArg list) : Context =
            Context(prog, currentDecl, List.append tpvars tvs, vars, pos, modulePath, importPaths, currMethod, inForLoopInitializer, inForLoopBody)

        member this.add(ds: LocalDecl list) : Context =
            Context(prog, currentDecl, tpvars, List.append vars ds, pos, modulePath, importPaths, currMethod, inForLoopInitializer, inForLoopBody)
        // abbreviation for a single non-ghost local variable
        member this.add(n: string, t: Type) : Context = this.add [ LocalDecl(n, t, false) ]

        /// remembers where we are
        member this.setPos(p: ContextPosition) = Context(prog, currentDecl, tpvars, vars, p, modulePath, importPaths, currMethod, inForLoopInitializer, inForLoopBody)
        member this.enterBody() = this.setPos(BodyPosition)
        
        /// enter a new module
        member this.enterModuleScope(newModulePath: Path)  =
            Context(prog, currentDecl, tpvars, vars, pos, modulePath.append(newModulePath), importPaths, currMethod, inForLoopInitializer, inForLoopBody)
        
        // add and remove imports
        member this.addImport(importType: ImportType) =
            Context(prog, currentDecl, tpvars, vars, pos, modulePath, importType :: importPaths, currMethod, inForLoopInitializer, inForLoopBody)
               
    (* ***** printer for the language above

       This is implemented as a class so that we can use state for indentation or overriding for variants.
       A new instance should be created for every print job.
    *)
    // F# has string interpolation now, so this code could be made more readable
    type Printer() =
        let UNIMPLEMENTED = "<UNIMPLEMENTED>"
        let indentString = "  "
        let indented(s: string, braced: Boolean) =
            let s = ("\n"+s).Replace("\n","\n"+indentString)
            if braced then " {" + s + "\n}\n" else s
        let indentedBraced(s: string) = indented(s,true)
        
        member this.prog(p: Program, pctx: PrintingContext) =
            // Print out includes first because Dafny enforces this.
            // For future work, consider making includes meta-information instead of
            // AST information, as this along with the design of Dafny includes as a
            // preprocessor-level syntax construct.
            
            let iPath (p: Path) =
                let toSysPath (Path plist) =
                    String.concat "/" plist                
                "include " + "\"" + toSysPath(p) + "\""
            
            let includes =
                List.collect (function | Include p -> [iPath p] | _ -> []) p.decls
                |> String.concat "\n"
                
            includes
            + "\n"
            + if not(p.meta.prelude.Equals("")) then
                "/***** TYPECART PRELUDE START *****/\n"
                + p.meta.prelude
                + "\n/***** TYPECART PRELUDE END *****/"
              else "\n"
            + this.declsGeneral(p.decls, pctx, false)

        member this.tpvar(inDecl: bool) (a: TypeArg) =
            // Only print out variance type info for declaration-level printing.
            // Prefix "+" for (n, Some true) and prefix "-" for (n, Some false).
            if inDecl then
                match a with
                | (n,None) -> n
                | (n,Some true) -> "+" + n
                | (n,Some false) -> "-" + n
            else
                match a with
                | (n,None) 
                | (n,Some true) 
                | (n,Some false) -> n
        // inDecl should only be set to true when printing out class or datatype declarations.
        // These are the only places when variance type signature should be print out.
        member this.tpvars(inDecl: bool)(ns: TypeArg list) =
            if ns.IsEmpty then
                ""
            else
                "<" + listToString (List.map (this.tpvar inDecl) ns, ", ") + ">"

        member this.declsGeneral(ds: Decl list, pctx: PrintingContext, braced: Boolean) =
                indented(listToString (List.map (fun d -> this.decl(d, pctx) + "\n\n") ds, ""), braced)
        member this.decls(ds: Decl list, pctx: PrintingContext) =
                this.declsGeneral(ds, pctx, true) 
        // array dimensions/indices
        member this.dims(ds: Expr list, pctx: PrintingContext) = "[" + this.exprsNoBr false ds ", " pctx + "]"
        member this.meta(_: Meta) = ""
        
        member this.methodType(m: MethodType) =
            match m with
            | NonStaticMethod mp -> mp.ToString()
            | StaticMethod mp -> "static " + mp.ToString()
                
        member this.decl(d: Decl, pctx: PrintingContext) =
            let comm = d.meta.comment |> Option.map (fun s -> "/* " + s + " */\n") |> Option.defaultValue ""
            let decls d = this.decls(d, pctx)
            let expr (f: bool) (e: Expr) : string = this.expr(f)(e)(pctx)
            // comm +
            match d with
            | Include p -> "" (* includes are printed out first *)
            | Module (n, ds, a) ->
                "module "
                + (this.meta a)
                + n
                + (decls ds)
            | Datatype (n, tpvs, cons, ds, a) ->
                let consS = List.map (fun x -> this.datatypeConstructor(x, pctx)) cons
                "datatype "
                + (this.meta a)
                + n
                + (this.tpvars true tpvs)
                + " = " 
                + listToString (consS, " | ")
                + (decls ds)
            | Class (n, isTrait, tpvs, p, ds, a) ->
                if isTrait then "trait " else "class "
                + (this.meta a)
                + n
                + (this.tpvars true tpvs)
                + if p.IsEmpty then
                      ""
                  else
                      (" extends "
                       + listToString (List.map this.classType p, ",")
                       + " ")
                + (decls ds)
            | TypeDef (n, tpvs, sup, predO, isNew, _) ->
                (if isNew then "newtype " else "type ")
                + n
                + (this.tpvars true tpvs)
                + " = "
                + (match predO with
                   | Some (x, p) -> this.localDecl(LocalDecl(x,sup,false)) + " | " + (this.expr false p pctx)
                   | None -> this.tp sup)
            | Field (n, t, eO, _, _, _, a) ->
                "const "
                + (this.meta a)
                + n
                + ": "
                + (this.tp t)
                + this.exprO(false)(eO, " := ", pctx)
            | Method (methodType, n, tpvs, ins, outs, b, _, _, _) ->
                let outputsS =
                    match outs.outputType with
                    | Some t -> this.tp t
                    | None -> this.localDecls outs.decls
                let methodCtx = pctx.enterMethod(n, methodType)
                this.methodType(methodType) + " "
                + n
                + (this.tpvars false tpvs)
                + (this.localDecls ins.decls)
                + (match methodType.map() with
                   | IsLemma | IsPredicate | IsPredicateMethod -> ""
                   | IsMethod -> " returns " + outputsS
                   | _ -> ":" + outputsS)
                + (this.conditions(true, ins.conditions, methodCtx))
                + (this.conditions(false, outs.conditions, methodCtx))
                + "\n"
                + Option.fold (fun _ e -> this.expr false e methodCtx) "" (Option.map block b)
            | ClassConstructor (n, tpvs, ins, outs, b, a) ->
                "constructor "
                + (this.meta a)
                + if n <> "_ctor" then n else ""
                + (this.tpvars false tpvs)
                + this.inputSpec(ins, pctx)
                + (this.conditions(false, outs, pctx))
                + "\n"
                + match b with
                  | Some e -> expr false e
                  | None -> "{}"
            | Import importT -> importT.ToString()
            | Export exportT -> exportT.ToString()
            | DUnimplemented -> UNIMPLEMENTED

        member this.inputSpec(ins: InputSpec, pctx: PrintingContext) =
            match ins with
            | InputSpec (lds, rs) ->
                this.localDecls lds
                + this.conditions (true, rs, pctx)

        member this.outputSpec(outs: OutputSpec, pctx: PrintingContext) =
          let r = match outs.outputType with
                  | Some t -> this.tp t
                  | None -> this.localDecls outs.decls
          r + this.conditions (false, outs.conditions, pctx)

        member this.conditions(require: bool, cs: Condition list, pctx: PrintingContext) =
            if cs.IsEmpty then "" else indented(listToString (List.map (fun c -> this.condition (require, c, pctx)) cs, "\n"), false)

        member this.condition(require: bool, c: Condition, pctx: PrintingContext) =
            let kw = if require then "requires" else "ensures"
            kw + " " + this.expr false c pctx

        member this.datatypeConstructor(c: DatatypeConstructor, pctx: PrintingContext) = c.name + (this.localDecls c.ins)

        member this.tps(ts: Type list) =
            if ts.IsEmpty then
                ""
            else
                "<"
                + listToString (List.map this.tp ts, ",")
                + ">"

        member this.tp(t: Type) = t.ToString()

        member this.exprsNoBr(isPattern: bool)(es: Expr list)(sep: string)(pctx: PrintingContext) =
            listToString (List.map (fun e -> this.expr isPattern e pctx) es, sep)

        member this.exprs(isPattern: bool)(es: Expr list)(pctx: PrintingContext) = "(" + (this.exprsNoBr isPattern es ", " pctx) + ")"

        member this.exprO(isPattern: bool)(eO: Expr option, sep: string, pctx: PrintingContext) =
            Option.defaultValue ("") (Option.map (fun e -> sep + (this.expr isPattern e pctx)) eO)

        member this.noPrintSep(e: Expr) =
            match e with
            | EIf _  // If-stmt without then-block
            | EFor _  // no trailing separator after for body-block
            | EWhile _ -> true
            | _ -> false
        
        member this.expr(isPattern: bool)(e: Expr)(pctx: PrintingContext) =
            let expr e = this.expr(isPattern)(e)(pctx)
            let exprs es = this.exprs(isPattern)(es)(pctx)
            let exprO (e, sep) = this.exprO(isPattern)(e, sep, pctx)
            let exprsNoBr p es sep = this.exprsNoBr(p)(es)(sep)(pctx)
            
            // if statements without then-blocks cannot have ";" after them. Afford special treatment for them.
            // The last statement is the return value in functions, so we do not prefix with ";" except in certain
            // cases like EAssert, EAssume.
            // To efficiently handle the last statement in a singly linked list, we first reverse the list
            // match on the last which is now the first, and then reverse the list back into the original order.
            let exprsNoBrBlock p es sep =
                let aux revEs =
                    match revEs with
                    | EAssert _ :: _ 
                    | EAssume _ :: _ 
                    | EBreak _ :: _
                    | EUpdate _ :: _ ->
                        List.map (fun e ->
                            if this.noPrintSep(e) then
                                (this.expr p e pctx)
                            else (this.expr p e pctx) + ";") revEs
                    | e :: t ->
                        let ps =
                            if pctx.inForLoopBody() then
                                match e with
                                | EReturn _ -> "" // We already print out ";" after an EReturn, printing twice causes dafny to complain.
                                | _ -> sep
                            else ""
                        let pctx = if pctx.inForLoopBody() then pctx.leaveForLoopBody() else pctx
                        (this.expr p e pctx) + ps ::
                        (List.map
                          (fun e ->
                            if this.noPrintSep(e) then
                                this.expr p e pctx
                            else (this.expr p e pctx) + sep) t)
                    | [] -> []
                aux (List.rev es) |> List.rev |> String.concat ""
            
            let dims ds = this.dims(ds, pctx)
            let receiver r = this.receiver(r, pctx)
            let case c = this.case c pctx
            let tp = this.tp
            let tps = this.tps

            match e with
            | EVar n ->
                let nF = n.Replace("_mcc#","mcc_") // Dafny-generated names that are not valid Dafny concrete syntax
                nF
            | EThis -> "this"
            | ENew (ct, _) -> "new " + this.classType (ct) + "()"
            | ENull _ -> "null"
            | EMemberRef (r, m, _) -> (receiver r) + m.name
            | EBool (v) -> match v with true -> "true" | false -> "false"
            | EChar (v) -> "'" + v.ToString() + "'"
            | EString (v) -> "\"" + v.ToString() + "\""
            // EToString compile from sequence display expressions of char sequences.
            | EToString (es) -> "[" + (exprsNoBr false es ", ") + "]"
            | EInt (v, _) -> v.ToString()
            | EReal (v, _) -> v.ToString()
            | EQuant (q, lds, r, b) ->
                "(" + q.ToString()
                + " "
                + this.localDeclsBr (lds,false)
                + " :: "
                + (match r with
                   | Some e -> expr e + (if q = Forall then " ==> " else " && ")
                   | None -> ""
                ) + (expr b) + ")"
            | EOld e -> "old(" + (expr e) + ")"
            | ETuple (es) -> exprs es
            | EProj (e, i) -> expr (e) + "." + i.ToString()
            | EFun (vs, _, e) -> (this.localDecls vs) + " => " + (expr e)
            | ESet (_, es) -> "{" + (exprs es) + "}"
            | ESetComp (lds, predicate) ->
                let ldsStr = List.map this.localDecl lds |> String.concat ", "
                "set (" + ldsStr + ") | " + (expr predicate)
            | ECharAt (s, i) -> (expr s) + dims ([ i ])
            | EStringRange (s, f, t) ->
                (expr s)
                + "["
                + exprO (f, "")
                + ".."
                + exprO (t, "")
                + "]"
            | ESeq (_, es) -> "[" + (exprsNoBr isPattern es ", ") + "]"
            | ESeqConstr(_, l, i) -> "seq(" + (expr l) + ", " + (expr i) + ")"
            | ESeqAt (s, i) -> (expr s) + "[" + (expr i) + "]"
            | ESeqRange (s, f, t) ->
                (expr s)
                + "["
                + exprO (f, "")
                + ".."
                + exprO (t, "")
                + "]"
            | ESeqUpdate (s, i, e) -> (expr s) + "[" + (expr i) + "] := " + (expr e)
            | EArray (t, d) -> "new " + t.ToString() + dims (d)
            | EArrayAt (a, i) -> (expr a) + dims (i)
            | EArrayRange (a, f, t) ->
                (expr a)
                + "["
                + exprO (f, "")
                + ".."
                + exprO (t, "")
                + "]"
            | EArrayUpdate (a, i, e) -> (expr a) + dims (i) + " := " + (expr e)
            | EMapAt (m, e) -> (expr m) + (dims [ e ])
            | EMapKeys (e) -> (expr e) + ".Keys"
            | EMapDisplay (elts) ->
                let str = List.fold (fun l (k, v) -> (String.concat " := " [expr k; expr v]) :: l) [] elts
                let str = String.concat " , " str
                "map [" + str + "]"
            | EMapComp (lds, p, tL, tR) ->
                let ldsStr = List.map this.localDecl lds |> String.concat ", "
                "map " + ldsStr + " | " + (expr p) + " :: " +
                match tL with
                | None -> expr tR
                | Some tL -> (expr tL) + " := " + (expr tR)
            | EUnOpApply (op, e) -> this.unaryOperator op (expr e)
            | EBinOpApply (op, e1, e2) -> this.binaryOperator op (expr e1) (expr e2)
            | EAnonApply (f, es) -> (expr f) + (exprs es)
            | EMethodApply (r, m, ts, es, _) ->
                (receiver r)
                + m.name
                + (exprs es)
            | EConstructorApply (c, ts, es) ->
                // let cS = if isPattern then c.name else c.ToString()
                c.name + (exprs es)
            | EBlock es ->
                // throw out empty blocks; these are usually artifacts of the processing
                let notEmptyBlock e = match e with | EBlock [] | ECommented(_,EBlock[]) -> false | _ -> true
                let esS = exprsNoBrBlock false (List.filter notEmptyBlock es) ";\n"
                let s = indentedBraced(esS)
                s
            | ELet (n, t, d, e) ->
                "var "
                + n
                + ":"
                + (tp t)
                + ":="
                + (expr d)
                + "; "
                + (expr e)
            | EIf (c, t, e) ->
                let printThen =
                    match pctx.inMethod() with
                    | Some (_, methodType) ->
                        match methodType.map() with
                        | IsMethod | IsLemma -> false
                        | _ -> true 
                    | _ -> true
                let elsePart =
                    match e with
                    | None -> "" // avoid using exprO which prints out ";".
                    | Some e -> " else " + expr e
                let s =
                    "if "
                    + (expr c)
                    + (if printThen then " then " else "")
                    + (expr t)
                    + elsePart
                s
            | EFor (index, init, last, up, body) ->
                let d =
                    EDecls [ (index, Some(plainUpdate init)) ]
                let forInitCtx = pctx.enterForLoopInitializer()
                let forBodyCtx = pctx.enterForLoopBody()
                "for "
                + this.expr(isPattern)(d)(forInitCtx)
                + (if up then " to " else " downto ")
                + (expr last)
                + " "
                + this.expr(isPattern)(body)(forBodyCtx)
            | EWhile (c, e, l) ->
                let label =
                    match l with
                    | Some l -> sprintf "%s: " l
                    | None -> ""

                sprintf "%swhile (%s)%s" label (expr c) (expr e)
            | EReturn (es) ->
                "return " + (exprsNoBr false es ", ") + ";"
            | EBreak l ->
                let label =
                    match l with
                    | Some l -> sprintf " %s" l
                    | None -> ""

                sprintf "break%s" label
            | EMatch (e, t, cases, dfltO) ->
                let defCase =
                    match dfltO with
                    | None -> []
                    | Some e -> [{vars = []; pattern = EWildcard; body = e}] // case _ => e
                let csS =
                    List.map (fun (c: Case) -> case c) (cases @ defCase)
                "match "
                + (expr e)
                + indentedBraced(listToString(csS, "\n"))
            | EDecls (ds) ->
                let doOne (ld: LocalDecl, uO: UpdateRHS option) =
                    let varQual =
                        if pctx.inForLoopInitializer() then "" else "var "
                    varQual
                    + (this.localDecl ld)
                    + (Option.defaultValue "" (Option.map (fun x -> this.update x pctx) uO))

                listToString (List.map doOne ds, ", ")
            | EUpdate (ns, u) ->
                let lhsExprs = List.map expr ns
                listToString (lhsExprs, ",") + (this.update u pctx)
            | EDeclChoice (ld, e) ->
                "var "
                + (this.localDecl ld)
                + " where "
                + (expr e)
            | ETypeConversion (e, toType) -> (expr e) + " as " + (tp toType)
            | EPrint es -> "print" + (String.concat ", " (List.map expr es))
            | EAssert e -> "assert " + (expr e) 
            | EAssume e -> "assume " + (expr e) + ";"
            | EReveal es -> "reveal " + (String.concat ", " (List.map expr es)) + ";"
            | ECommented(s,e) -> "/* " + s + " */ " + expr e
            | EUnimplemented -> UNIMPLEMENTED

        member this.binaryOperator(op: string) (eSL : string) (eSR : string) : string =
            // TODO: handle operator precedence? See dafny Printer.cs for precedence.
            // reconstruct dafny Opcode by converting string back to enum.
            let mutable eOp = BinaryExpr.ResolvedOpcode.YetUndetermined
            if Enum.TryParse<BinaryExpr.ResolvedOpcode>(op, &eOp) then
                "(" + eSL + " " + (eOp |> BinaryExpr.ResolvedOp2SyntacticOp |> BinaryExpr.OpcodeString) + " " + eSR + ")"
            else
                failwith $"unsupported binary operator %s{op}"
            

        // For reference, see unary expression handling in dafny Printer.cs file.
        member this.unaryOperator(op : string) (eS : string) =
            match op with
            | "Not" -> "!" + eS
            | "Cardinality" -> "|" + eS + "|"
            | "Fresh" -> "fresh(" + eS + ")"
            | "Allocated" -> "allocated(" + eS + ")"
            | "Lit" -> "Lit(" + eS + ")"
            | _ -> failwith $"unsupported unary operator %s{op}"
            
        
        member this.localDeclsBr(lds: LocalDecl list, brackets: bool) =
            (if brackets then "(" else "")
            + listToString (List.map this.localDecl lds, ", ")
            + (if brackets then ")" else "")
        member this.localDecls(lds: LocalDecl list) = this.localDeclsBr(lds,true)

        member this.update(u: UpdateRHS)(pctx: PrintingContext) =
            let op = if u.monadic.IsSome then ":-" else ":="
            " " + op + " " + (this.expr false u.df pctx)

        member this.localDecl(ld: LocalDecl) = ld.name + ": " + (this.tp ld.tp)
        
        member this.classType(ct: ClassType) =
            ct.path.ToString() + (this.tps ct.tpargs)
        
        member this.receiver (rcv: Receiver, pctx: PrintingContext) =
            // do not print out the "." separator if receiver is empty.
            let dot s =
                match s with
                | "" -> ""
                | _ -> s + "."
            match rcv with
            | StaticReceiver (ct) -> this.classType(ct) |> dot // ClassType --> path, tpargs
            | ObjectReceiver (e) -> this.expr false e pctx |> dot

        member this.case(case: Case)(pctx: PrintingContext) =
            "case " + this.expr true case.pattern pctx
            + " => "
            + indented(this.expr false case.body pctx, false)

    // shortcut to create a fresh printer
    let printer () = Printer()
    
    // shortcut to an empty context
    let emptyPrintingContext = EmptyPrintingContext()
