module New.A {

	// base type synonym
	type intAltEq = int

	type neq = set<bool>

	// datatype with same (syntactic) type synonym
	datatype fooEq = A1(x: intAltEq) | A2

	// datatype with substituted type synonym
	datatype subSyNeq = B1(x: int) | B2(x: intAltEq)

	// type synonym of datatype
	type fooAltEq = fooEq

	// datatype of type synonym of datatype
	datatype nestedSyNeq = C1(x: fooEq) | C2(y: fooAltEq) | C3(z: fooAltEq)

	// type synonym of newtype
	newtype boundEq = x : int | 9 <= x <= 47

	type boundAltEq = boundEq

	datatype newSynDataEq = D1(x: boundAltEq)

	//subs in newtype
	datatype newSynDataSubEq = E1(x: boundAltEq) | E2(y: boundEq) | E3(z: boundAltEq)

	// subs in int
	datatype newSynDataNeq = F1(y: int) | F2(z: boundEq)

	// datatype using bad synonym
	datatype usesNeq = G1(b: neq)

	// datatype with same (non-syntactic) synonym
	type intAltAltEq = int

	datatype diffSyntaxSameType = F1(i: intAltAltEq, j: intAltEq)

	// datatype using type synonym for bad newtype
	newtype neqNew = x : int | 0 <= x <= 81
	type neqNewAlt = neqNew
	datatype usesNeqNew = G1(l: seq<neqNew>)

}
