TypeCart
------------

[![.NET build](https://github.com/awslabs/typecart/actions/workflows/dotnet.yml/badge.svg?branch=dev)](https://github.com/awslabs/typecart/actions/workflows/dotnet.yml) 

**typeCart** is an analysis tool for proof evolution to facilitate proof maintenance for continuously integrated software. typeCart is constructed in F# and it

1. reads two Dafny files into Dafny AST,
2. analyses the ASTs to identify syntactically equivalent types between them, and
3. generates mapping functions between equivalent types.

Additionally, typeCart generates the verification contracts (Dafny's `require` and `ensure` clauses) for the mapping functions, enabling the Dafny verifier to successfully verify the generated functions. Such functions helps proof engineers in estimating a quantitative measure about incremental changes between two version of the same specs written in Dafny.

**Trivia:** `Cart` in `typeCart` represents cartography: typeCart generates mapping functions for equal types.

See [examples and features](docs/ExamplesFeatures.md).

## Build

typeCart builds on [.NET 6.0](https://dotnet.microsoft.com/en-us/download/dotnet/5.0). To build typeCart, simply invoke `dotnet build` in the following three project folders:

 - `TypeInjections/TypeInjections`: Main typeCart program. To use typeCart, run the compiled program on two dafny files, two directories containing a dafny project each, with an optional argument being a list of regex dictating what files typeCart should ignore in the directory.  The regexes would match on the ignored filenames, and `.` and `/` needn't be escaped.
 - `TypeInjections/TypeInjections.Test`: Tests for typeCart
 - `TypeInjections/Tool`: dotnet CLI tool for typeCart.





**Contributions are welcomed!** See [CONTRIBUTING](CONTRIBUTING.md) guidelines for more information.

## License

typeCart is distributed under MIT license, see [LICENSE.txt](LICENSE.txt) for details.

