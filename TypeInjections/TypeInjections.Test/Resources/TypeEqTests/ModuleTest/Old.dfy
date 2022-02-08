// Only the "sameModuleEq" types are equal

module Old.A {

	datatype sameModuleEq = A | B(x: seq<int>)

	datatype sameModuleNeq = C(y : bool) | D(x: set<sameModuleNeq>)

	// same (syntactically) as New.B.diffModuleEq
	datatype diffModuleEq<A> = E(x:A) | F(s: diffModuleEq)
}

module Old.B {

	datatype sameModuleEq = A(y: set<char>) | B

	datatype sameModuleNeq = C(y : sameModuleNeq) | D(x: set<bool>)

	// same (syntactically) as New.A.diffModuleEq
	datatype diffModuleEq<A> = E(x : A) | F(s: seq<A>)

	datatype DiffModuleDiffSnd<A> = G | H(a: bool) | I(s: seq<seq<seq<set<A>>>>)

}
