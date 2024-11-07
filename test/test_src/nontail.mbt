fn nontail(x: Int, acc: Int) -> Int {
    if (x <= 0) {
        acc
    } else {
        let a = nontail(x - 1, acc + x);
        nontail(x - 2, acc + a)
    }
};

// Answer: 2613
fn main {
    print_int(nontail(5, 0))
};