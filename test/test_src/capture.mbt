fn cs() -> Int {
    12
};

fn wrapper() -> Int {
    let i = Array::make(1, 10);
    let v = cs() - cs() * 5 / 6;

    fn f() -> Int {
        let one = cs() / 12;

        fn g(z) {
            if (0 <= z) {
                g(z - one) + z
            } else {
                if (i[0] == 0) {
                    0
                } else {
                    i[0] = i[0] - 1;
                    f()
                }
            }
        };

        g(cs()) + v
    };

    f()
};

// Answer: 880
fn main {
    print_int(wrapper())
};