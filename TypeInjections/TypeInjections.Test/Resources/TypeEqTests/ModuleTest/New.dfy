// Only the "sameModuleEq" types are equal

module New.A {

	datatype sameModuleEq = A | B(x: seq<int>)

	datatype sameModuleNeq = C(y : bool) | D(x: seq<sameModuleNeq>)

	// same (syntactically) as Old.B.diffModuleEq
	datatype diffModuleEq<A> = E(x : A) | F(s: seq<A>)

	datatype DiffModuleDiffSnd = G | H(a: int) | I(s: string)
}

module New.B {

	datatype sameModuleEq = A(y: set<char>) | B

	datatype sameModuleNeq = C(y : sameModuleNeq) | D(x: set<sameModuleEq>)

	// same (syntactically) as Old.A.diffModuleEq
	datatype diffModuleEq<A> = E(x:A) | F(s: diffModuleEq)

}
