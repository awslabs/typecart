**typeCart** is an analysis tool for proof evolution to facilitate proof maintenance for continuously integrated software. typeCart is constructed in F# and it

1. reads two Dafny files into Dafny AST,
2. analyses the ASTs to identify syntactically equivalent types between them, and
3. generates mapping functions between equivalent types.

Additionally, typeCart generates the verification contracts (Dafny's `require` and `ensure` clauses) for the mapping functions, enabling the Dafny verifier to successfully verify the generated functions. Such functions helps proof engineers in estimating a quantitative measure about incremental changes between two version of the same specs written in Dafny.

**Trivia:** `Cart` in `typeCart` represents cartography: typeCart generates mapping functions for equal types.

## Build

typeCart builds on [.NET 5.0](https://dotnet.microsoft.com/en-us/download/dotnet/5.0), it supports Dafny 3.3.0 and Z3 4.8.5. The Makefile is configured to install Dafny and Z3 locally in the root directory. After installing .NET 5.0, run in the root directory 
```
> make
```
to build the project. 

To run tests, use
```
> make test
```
Other `make` options: `deps, check_format, clean`

## Security

See [CONTRIBUTING](CONTRIBUTING.md#security-issue-notifications) for more information.

## License

typeCart is distributed under MIT license, see [LICENSE.txt](LICENSE.txt) for details.

