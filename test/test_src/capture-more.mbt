fn main {
    fn id() { () };
    let t = Array::make(10, id);

    let i = Array::make(1, 9);
    fn f() {
        if (i[0] == -1) {
            ()
        } else {
            let x = i[0];

            fn g() {
                print_int(x)
            };

            t[i[0]] = g;

            i[0] = i[0] - 1;
            f()
        }
    };
    
    let _ = f();

    fn call(x) {
        if (x == 10) {
            ()
        } else {
            let _ = t[x]();
            call(x + 1)
        }
    };

    call(0)
};