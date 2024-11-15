enum T {
    Add(T, T)
    Sub(T, T)
    Lit(Int)
};

fn eval(t: T) -> Int {
    match t {
        Add(a, b) => eval(a) + eval(b)
        Sub(a, b) => eval(a) - eval(b)
        Lit(a) => a
    }
};

fn main {
    let e = Add(Lit(4), Sub(Lit(3), Lit(2)));
    print_int(eval(e))
};