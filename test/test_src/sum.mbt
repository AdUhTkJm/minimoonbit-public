let x: () -> Int = {
    let g = 1;
    fn h() { g }
    h
};