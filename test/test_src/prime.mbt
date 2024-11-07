let arr: Array[Bool] = Array::make(100, true);

let w: Unit = {
    arr[0] = false;
    arr[1] = false;
    ()
};

let do_it: Unit = {
    fn go(x, i) {
        if (100 <= x) {
            ()
        } else {
            arr[x] = false;
            go(x + i, i)
        }
    };

    fn sift(x) {
        if (10 <= x) {
            ()
        } else {
            let _ = if (arr[x]) {
                go(x + x, x)
            };
            sift(x + 1)
        }
    };

    sift(2)
};

let output: Unit = {
    fn sum(x, acc: Int) -> Int {
        if (100 <= x) {
            acc
        } else {
            if (arr[x]) {
                sum(x + 1, acc + 1)
            } else {
                sum(x + 1, acc)
            }
        }
    };

    print_int(sum(0, 0))
};

fn main {
    print_endline()
};