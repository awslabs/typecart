module Functions {
    type Input = i: nat | i < 2
    type Output = i: nat | i < 2
    function g(f: Input -> Output, x: Input): Output {
        f(x)
    }
    function f1(x: Input): Output {
        x
    }
    function f2(x: Input): Output {
        0
    }
    function test(x: Input): nat {
        f1(x) as nat + f2(x) as nat
    }
}
