let n: Int = 7;

let arr: Array[Int] = Array::make(n, 0);

let is_end: Array[Bool] = Array::make(1, false);

let g: Unit = {
    fn fill(x) {
        if (x == n) {
            ()
        } else {
            arr[x] = x + 1;
            fill(x + 1)
        }
    };
    fill(0)
};

fn reverse(arr: Array[Int], start: Int, end: Int) -> Unit {
    if (start <= end) {
        let temp = arr[start];
        arr[start] = arr[end];
        arr[end] = temp;
        reverse(arr, start + 1, end - 1)
    } else {
        ()
    }
};

// Modifies arr 
fn next_permutation(arr: Array[Int]) -> Bool {

    // Find the rightmost place where arr[i] < arr[i + 1]
    fn get_asc(i: Int) {
        if (0 <= i) {
            if (arr[i + 1] <= arr[i]) {
                get_asc(i - 1)
            } else {
                i
            }
        } else {
            i
        }
    };

    let i = get_asc(n - 2);

    // If no such place, we reached the end
    let ret =
        if not(0 <= i) {
            true
        } else {

            // Otherwise, get the rightmost element greater than arr[i]
            fn get_big(j: Int) {
                if (arr[j] <= arr[i]) {
                    get_big(j - 1)
                } else {
                    j
                }
            };

            let j = get_big(n - 1);

            let t = arr[i];
            arr[i] = arr[j];
            arr[j] = t;

            let _ = reverse(arr, i + 1, n - 1);
            false
        };

    ret
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

// Function to calculate the flip count for a given permutation
fn flip_count(arr: Array[Int]) -> Int {
    let copy = Array::make(n, 0);

    let _ = memcpy(copy, arr, 0, 0, n);
    
    fn cnt(acc) {
        if not(copy[0] == 1) {
            let k = copy[0];
            let _ = reverse(copy, 0, k - 1);
            cnt(acc + 1)
        } else {
            acc
        }
    };
    cnt(0)
};

fn max(a: Int, b: Int) -> Int {
    if (a <= b) {
        b
    } else {
        a
    }
};

fn fannkuch(n: Int) -> Int {
    let mx = Array::make(1, 0);

    fn do_loop() {
        mx[0] = max(mx[0], flip_count(arr));
        if not(next_permutation(arr)) {
            do_loop()
        } else {
            mx[0]
        }
    };

    do_loop()
};

fn print_array(arr: Array[Int]) -> Unit {
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
    print_int(fannkuch(7))
};