module Old.A {

	datatype constructorDiffOrderEq = A2(b: bool) | A1(a: int)

	datatype constructorDiffOrderNeq = B2(b: int) | B1(a: bool)

	datatype constructorDiffOrderPermEq = C3 | C1 | C4 | C2 | C6 | C5

	datatype genericRenameSimpleEq<B> = D1(x: seq<B>) | D2(y: B)

	//not interesting on its own; used below
	datatype eitherEq<A, B> = Left(x: A) | Right(y: B)

	datatype genericRenameComplexEq<K, L, M> = E1(x: K) | E2(y: seq<set<L>>) | E3(z: eitherEq<L, M>)

	// does not use same generic args everywhere
	datatype genericRenameSimpleNeq<B, A> = F1(x: A) | F2(y: B)

	// wrong types in the eitherEq params
	datatype genericRenameComplexNeq<K, L, M> = G1(x: K) | G2(y: seq<set<L>>) | G3(z: eitherEq<M, L>)
}
