fn random(state: Int) -> Int {
    state * 75 + 74
};

fn modulo(x: Int, y: Int) -> Int {
    let q = x / y;
    x - q * y
};

fn fill_buffer(v: (Int, Int, Array[Int]), n: Int) -> (Int, Int, Array[Int]) {
    let mutable = Array::make(1, v);
    fn aux(i: Int, state: Int) -> Unit {
        if i == n {
            ()
        } else {
            let new_state = random(state);
            let res = modulo(new_state, 65537);
            mutable[0] = push(mutable[0], res);
            aux(i + 1, res)
        }
    };
    let _ = aux(0, 12345);
    mutable[0]
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

fn vector() -> (Int, Int, Array[Int]) {
    let len = 0;
    let cap = 3;
    (len, cap, Array::make(cap, 0))
};

fn push(x: (Int, Int, Array[Int]), val: Int) -> (Int, Int, Array[Int]) {
    let (len, cap, arr) = x;
    if (len == cap) {
        let new_cap = truncate(float_of_int(cap) * 1.618);
        let new = Array::make(new_cap, 0);
        let _ = memcpy(new, arr, 0, 0, len);
        new[len] = val;
        (len + 1, new_cap, new)
    } else {
        arr[len] = val;
        (len + 1, cap, arr)
    }
};

fn print_vec(x: (Int, Int, Array[Int])) -> Unit {
    let (len, _, arr) = x;
    fn aux(z) {
        if (z == len) {
            ()
        } else {
            let _ = print_int(arr[z]);
            let _ = print_char(32);
            aux(z + 1)
        }
    };
    aux(0)
};

fn main {
    let v = vector();
    let filled = fill_buffer(v, 30);
    let (len, cap, _) = filled;
    let _ = print_int(len);
    let _ = print_endline();
    let _ = print_int(cap);
    let _ = print_endline();
    print_vec(filled)
};