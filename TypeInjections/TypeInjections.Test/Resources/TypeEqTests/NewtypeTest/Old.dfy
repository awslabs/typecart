module Old.A {

	// tests for expression equivalence
	newtype noVarNoCondEq = int

	newtype varTrivialCondEq = x : int | true

	newtype varImpossibleEq = x : real | false

	newtype varEq = x : int | x == 3

	newtype varLt = x : int | x < 10

	newtype varLe = x : real | x <= 5.0

	newtype varGt = x : int | x > -8

	newtype varGe = x : int | x >= 10

	newtype varLeGe = x : int | 0 <= x <= 5

	newtype varLtGe = x : int | 0 <= x < 9

	newtype varLeGt = x : int | 0 < x <= -1

	newtype varLtGt = x : int | -90 < x < -5

	// non-equivalent expressions
	newtype noVarNoCondNeq = int

	newtype boolNeq = x : int | true

	newtype litNeq = x : int | 10 <= x

	newtype opNeq = x : real | 9.0 <= x

	newtype oneSameOneNeq = x : int | 0 <= x < 7

	// other properties
	newtype typeNeq = x : int | 0 <= x

	// this is just a dummy variable
	newtype varDiffTypeEq = x : int | 0 <= x < 5

	newtype compoundExpEq = x : int | 0 <= x && 9 <= x && -1 < x

	newtype compoundSubstMultipleEq = x : int | 0 <= x && 9 <= x && -1 < x

	// Use newtype in a datatype
	datatype fooEq = A1(x: int) | A2(y: varLtGe)

	datatype barNeq = B1 | B2(x: oneSameOneNeq)

}
