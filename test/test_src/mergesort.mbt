fn random(state: Int) -> Int {
    state * 75 + 74
};

fn modulo(x: Int, y: Int) -> Int {
    let q = x / y;
    x - q * y
};

fn fill_buffer(arr: Array[Int], n: Int) -> Unit {
    fn aux(i: Int, state: Int) -> Unit {
        if i == n {
            ()
        } else {
            let new_state = random(state);
            let res = modulo(new_state, 65537);
            arr[i] = res;
            aux(i + 1, res)
        }
    };
    aux(0, 12345)
};

fn memcpy(dest: Array[Int], src: Array[Int], off_x: Int, off_y: Int, len: Int) -> Unit {
    fn aux(i) {
        if (i == len) {
            ()
        } else {
            dest[off_x + i] = src[off_y + i];
            aux(i + 1)
        }
    };
    aux(0)
};

fn mergesort(x: Array[Int], begin: Int, end: Int) -> Unit {
    if (2 <= end - begin) {
        let mid = (begin + end) / 2;
        let _ = mergesort(x, begin, mid);
        let _ = mergesort(x, mid, end);
        let buffer = Array::make(end - begin, 0);
        fn aux(top, i, j) {
            if (i == mid) {
                (top, i, j)
            } else {
                if (j == end) {
                    (top, i, j)
                } else {
                    if (x[i] <= x[j]) {
                        buffer[top] = x[i];
                        aux(top + 1, i + 1, j)
                    } else {
                        buffer[top] = x[j];
                        aux(top + 1, i, j + 1)
                    }
                }
            }
        };
        let (top, i, j) = aux(0, begin, mid);
        let _ = memcpy(buffer, x, top, i, mid - i);
        let _ = memcpy(buffer, x, top, j, end - j);
        let _ = memcpy(x, buffer, begin, 0, end - begin);
        ()
    } else {
        ()
    }
};

// Does this comment work?
fn print_array(arr: Array[Int], n: Int) -> Unit {
    fn aux(i: Int) -> Unit {
        if i == n {
            ()
        } else {
            let _ = print_int(arr[i]);
            let _ = print_char(32);
            aux(i + 1)
        }
    };
    aux(0)
};

fn main {
    let a = Array::make(20, 0);
    let _ = fill_buffer(a, 20);
    let _ = mergesort(a, 0, 20);
    print_array(a, 20)
};