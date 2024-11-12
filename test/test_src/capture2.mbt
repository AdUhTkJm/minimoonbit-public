fn generate_adders(n: Int) -> Array[(Int) -> Int] {
    fn f(x) { x };
    let adders = Array::make(n, f);
    fn aux(i) {
        if (i == n) {
            ()
        } else {
            fn adder(x) { x + i };
            adders[i] = adder;
            aux(i + 1)
        }
    };
    let _ = aux(0);
    adders
};

fn main {
    let n = 100;
    let adders = generate_adders(n);
    fn aux(i, acc) {
        if (i == n) {
            acc
        } else {
            aux(i + 1, adders[i](acc))
        }
    };
    print_int(aux(0, 0))
};