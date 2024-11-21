template add of T: (a: T, b: T) -> T {
    a + b
};
end


fn main {
    let _ = print_int(add(Int)(2, 3));
    print_int(truncate(add(Double)(2.0, 3.0)))
};