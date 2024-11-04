fn f(x: Int) -> Int {
    x + 1
};

let g: (((Int) -> Int) -> (Int) -> Int) -> (Int) -> Int = {
    fn h(k) -> (Int) -> Int {
        k(f)
    };
    h
};

fn main {
    fn k(f) {
        fn w(x) {
            f(x + 2)
        };
        w
    };
    print_int(g(k)(3))
};