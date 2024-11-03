fn f(x: Int) -> Int {
    x + 1
};

let g: (Int) -> Int = f;

fn main {
    print_int(g(3))
};