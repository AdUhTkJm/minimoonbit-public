fn sum(x: Int) -> Int {
    match x {
        0 => 0
        n => sum(n - 1) + n
    }
};

fn main {
    print_int(sum(10000))
};