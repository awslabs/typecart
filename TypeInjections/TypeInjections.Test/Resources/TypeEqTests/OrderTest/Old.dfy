module Old.A {

	datatype constructorDiffOrderEq = A1(a: int) | A2(b: bool)

	datatype constructorDiffOrderNeq = B1(a: int) | B2(b: bool)

	datatype constructorDiffOrderPermEq = C1 | C2 | C3 | C4 | C5 | C6

	datatype genericRenameSimpleEq<A> = D1(x: seq<A>) | D2(y: A)

	//not interesting on its own; used below
	datatype eitherEq<A, B> = Left(x: A) | Right(y: B)

	datatype genericRenameComplexEq<A, B, C> = E1(x: A) | E2(y: seq<set<B>>) | E3(z: eitherEq<B, C>)

	// does not use same generic args everywhere
	datatype genericRenameSimpleNeq<A, B> = F1(x: A) | F2(y: B)

	// wrong types in the eitherEq params
	datatype genericRenameComplexNeq<A, B, C> = G1(x: A) | G2(y: seq<set<B>>) | G3(z: eitherEq<B, C>)
}
