fn cs() -> Int { 12 };

fn wrapper() -> (Int) -> Int {
    let y = cs();
    fn f(x) {
        if (x == 0) {
            1
        } else {
            let q = f(x - 1) + y;
            q
        }
    };
    f
};

fn main {
    let f = wrapper();
    print_int(f(10))
};