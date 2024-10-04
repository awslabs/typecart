module Functions {
    function get_adder(): (real, real) -> real {
        (a: real, b: real) => a + b
    }
    function add(adder: (real, real) -> real, a: real, b: real): real {
        adder(a, b)
    }
}
