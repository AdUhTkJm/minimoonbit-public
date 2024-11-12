fn create_closures(x: Int) -> (() -> Int, () -> Int) {
    fn use_x() { x };
    let a = use_x;
    let b = a;
    (a, b)
};

fn main {
    let (f, g) = create_closures(100);
    let _ = print_int(f());
    let _ = print_int(g());
    ()
};