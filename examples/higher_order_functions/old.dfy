module Functions {
    function get_adder(): (int, int) -> int {
        (a: int, b: int) => a + b
    }
    function add(adder: (int, int) -> int, a: int, b: int): int {
        adder(a, b)
    }
}
