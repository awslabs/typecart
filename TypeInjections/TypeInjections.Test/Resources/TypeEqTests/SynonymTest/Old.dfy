module Old.A {

	// base type synonym
	type intAltEq = int

	type neq = string

	// datatype with same (syntactic) type synonym
	datatype fooEq = A1(x: intAltEq) | A2

	// datatype with substituted type synonym
	datatype subSyNeq = B1(x: intAltEq) | B2(x: int)

	// type synonym of datatype
	type fooAltEq = fooEq

	// datatype of type synonym of datatype
	datatype nestedSyNeq = C1(x: fooAltEq) | C2(y: fooEq) | C3(z: fooAltEq)

	// type synonym of newtype
	newtype boundEq = x : int | 9 <= x <= 47

	type boundAltEq = boundEq

	datatype newSynDataEq = D1(x: boundAltEq)

	//subs in newtype
	datatype newSynDataSubEq = E1(x: boundEq) | E2(y: boundAltEq) | E3(z: boundAltEq)

	// subs in int
	datatype newSynDataNeq = F1(y: boundEq) | F2(z: int)

	// datatype using bad synonym
	datatype usesNeq = G1(b: neq)

	// datatype with same (non-syntactic) synonym
	type intAltAltEq = int

	datatype diffSyntaxSameType = F1(i: intAltEq, j: intAltAltEq)

	// datatype using type synonym for bad newtype
	newtype neqNew = x : int | 0 <= x <= 80
	type neqNewAlt = neqNew
	datatype usesNeqNew = G1(l: seq<neqNew>)

}
