fn random(state: Double) -> Double {
    state * 75.0 + 74.0
};

fn modulo(x: Double, y: Double) -> Double {
    let q = x / y;
    x - q * y
};

fn concat() {
    // ...
}

fn filter(x: Array[Double], len: Int, pred: (Double) -> Bool) -> (Array[Double], Int) {
    fn aux(x, len) {
        if (len == 0) {
            (x, 0)
        } else {
            if (pred(x[0])) {
                aux()
            } else {
                aux(x[1], len)
            }
        }
    };
    aux(x, len)
}

fn qsort(x: Array[Double], len: Int) -> Array[Double] {
    if (len == 0) {
        x
    } else {
        let pivot = x[0];
        fn smaller(a) {
            a < pivot
        };
        fn greater(a) {
            a > pivot
        };
        let left = filter(x, len, smaller);
        let right = filter(x, len, greater);
        // TODO: concat(left, pivot, right)
    }
};