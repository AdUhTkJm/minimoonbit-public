fn f() -> () -> Int {
    let x = 1;
    fn k() {
        x + 2
    };
    k
};

fn id(f: () -> () -> Int) -> () -> () -> Int {
    f
};

let g: () -> () -> Int = f;

let h: () -> () -> Int = id(g);

fn init {
    print_int(h()())
};