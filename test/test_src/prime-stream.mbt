fn filter(stream: () -> Int, pred: (Int) -> Bool) -> () -> Int {
    fn result() {
        let next = stream();
        if (pred(next)) {
            next
        } else {
            result()
        }
    };
    result
};

fn integers() -> () -> Int {
    let i = Array::make(1, 1);
    fn counter() {
        i[0] = i[0] + 1;
        i[0]
    };
    counter
};

fn divisible(by: Int) -> (Int) -> Bool {
    fn pred(x) {
        x / by * by == x
    };
    pred
};

fn no(f: (Int) -> Bool) -> (Int) -> Bool {
    fn negate(x) {
        not(f(x))
    };
    negate
};

fn primes(limit: Int) -> Int {
    let stream = integers();
    fn do_loop(stream: () -> Int, acc) {
        let next = stream();
        if not(next <= limit) {
            acc
        } else {
            do_loop(filter(stream, no(divisible(next))), acc + 1)
        }
    };

    do_loop(stream, 0)
};

fn main {
    print_int(primes(100))
};