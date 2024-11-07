fn init {
    let t = 7 * 109;
    let z = 18;
    let _ = print_int(1 - t * z);
    print_endline()
};

let arr: Array[Int] = Array::make(1, 0);

fn f() -> Int {
    2
};

fn id(f: () -> Int) -> () -> Int {
    f
};

let w: () -> Int = id(f);

let ww: Unit = {
    arr[0] = w();
    ()
};

let zz: Unit = print_int(arr[0]);

let endline: Unit = print_endline();

fn init {
    let _ = print_int(66 * 82);
    print_endline()
};

fn main {
    print_int(12)
};