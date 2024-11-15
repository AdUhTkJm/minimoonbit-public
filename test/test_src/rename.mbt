fn cs() -> Int { 1 };

let x: Int = 1;

fn main {
    let x = cs() + 8;
    let x = float_of_int(x) + 1.0;
    print_int(truncate(x))
};