pub struct OptEnv {
    // All names used in the program
    mut used_names: @immut/hashset.T[@types.Name]

    mut subexpr: Map[Expr, Name]

    mut alias: Map[Name, Name]
}

let e: OptEnv = OptEnv :: {
    used_names: @immut/hashset.T::new(),
    subexpr: Map::new(),
    alias: Map::new(),
}

fn OptEnv::add_used(self: OptEnv, arr: Array[Name]) -> Unit {
    self.used_names = union(self.used_names, @immut/hashset.T::from_array(arr));
}

fn get_used(expr: Expr) -> Unit {
    match expr {
        Add(a, b) | Sub(a, b) | Mul(a, b) | Div(a, b) |
        FAdd(a, b) | FSub(a, b) | FMul(a, b) | FDiv(a, b) |
        Eq(a, b) | Le(a, b) | ArrayGet(a, b) | Save(a, b) =>
            e.add_used([a, b]);

        Neg(a) | BNeg(a) | FNeg(a) | Var(a) | PackClosure(a) |
        Deref(a) | LShift(a, _) =>
            e.add_used([a]);

        Unit | Int(_) | Double(_) =>
            ();

        IfEq(a, b, body, otherwise) |
        IfLe(a, b, body, otherwise) => {
            e.add_used([a, b]);
            get_used(body);
            get_used(otherwise);
        }

        Let(_, val, w) => {
            get_used(val);
            get_used(w);
        }

        LetTuple(_, val, w) => {
            e.add_used([val]);
            get_used(w);
        }

        Call(a, arr) | CallTailRec(a, arr) | CallClosure(a, arr) =>
            e.add_used([..arr, a]);

        MakeTuple(arr) | CallExternal(_, arr) =>
            e.add_used(arr);

        ArrayPut(x, i, val) =>
            e.add_used([x, i, val]);
    }
}

fn side_effect_free(expr: Expr) -> Bool {
    match expr {
        Call(f, _) | CallTailRec(f, _) | CallClosure(f, _) => {
            @knf.e.is_se_free[f] == Some(true)
        }
        CallExternal(name, _) =>
            ["read_int", "read_char", "print_int", "print_char",
            "print_endline", "minimbt_malloc", "minimbt_create_ptr_array"].contains(name._)
        IfEq(_, _, body, otherwise) | IfLe(_, _, body, otherwise) =>
            side_effect_free(body) && side_effect_free(otherwise)
        Let(_, val, w) =>
            side_effect_free(val) && side_effect_free(w)
        LetTuple(_, _, w) =>
            side_effect_free(w)
        Save(_) => false
        _ => true
    }
}

fn used(name: Name) -> Bool {
    return e.used_names.contains(name);
}

// Removes all unused instances of a variable
fn opt_remove_unused_(expr: Expr) -> Expr {
    match expr {
        Let(a, val, w) => {
            if (used(a).not() && side_effect_free(val)) {
                opt_remove_unused_(w);
            } else {
                Let(a, opt_remove_unused_(val), opt_remove_unused_(w));
            }
        }
        LetTuple(x, arr, w) =>
            LetTuple(x, arr, opt_remove_unused_(w))
        IfLe(a, b, body, otherwise) =>
            IfLe(a, b, opt_remove_unused_(body), opt_remove_unused_(otherwise))
        IfEq(a, b, body, otherwise) =>
            IfEq(a, b, opt_remove_unused_(body), opt_remove_unused_(otherwise))
        t => t
    }
}

pub fn opt_remove_unused(program: Program) -> Program {
    e.used_names = @immut/hashset.T::new();
    for x in program.fundefs {
        get_used(x.body);
    }
    for x in program.fundefs {
        x.body = opt_remove_unused_(x.body);
    }
    // Can't do it for program.body;
    // can't easily determine if global variable has been used
    return program;
}

fn no_mutable(expr: Expr) -> Bool {
    match expr {
        IfEq(_, _, body, otherwise) | IfLe(_, _, body, otherwise) =>
            no_mutable(body) && no_mutable(otherwise)
        Let(_, val, w) =>
            no_mutable(val) && no_mutable(w)
        LetTuple(_, _, w) =>
            no_mutable(w)
        Deref(_) => false
        Save(_) => false
        _ => true
    }
}

fn rename(expr: Expr, f: (Name) -> Name) -> Expr {
    match expr {
        Neg(a) => Neg(f(a))
        Add(a, b) => Add(f(a), f(b))
        Sub(a, b) => Sub(f(a), f(b))
        Mul(a, b) => Mul(f(a), f(b))
        Div(a, b) => Div(f(a), f(b))
        FAdd(a, b) => FAdd(f(a), f(b))
        FSub(a, b) => FSub(f(a), f(b))
        FMul(a, b) => FMul(f(a), f(b))
        FDiv(a, b) => FDiv(f(a), f(b))
        FNeg(a) => FNeg(f(a))
        BNeg(a) => BNeg(f(a))
        Eq(a, b) => Eq(f(a), f(b))
        Le(a, b) => Le(f(a), f(b))
        IfEq(a, b, body, otherwise) => IfEq(f(a), f(b), rename(body, f), rename(otherwise, f))
        IfLe(a, b, body, otherwise) => IfLe(f(a), f(b), rename(body, f), rename(otherwise, f))
        Let(x, val, w) => Let(x, rename(val, f), rename(w, f))
        Var(a) => Var(f(a))
        Call(ff, args) => Call(f(ff), args.map(f))
        CallTailRec(ff, args) => CallTailRec(f(ff), args.map(f))
        CallClosure(ff, args) => CallClosure(f(ff), args.map(f))
        CallExternal(name, args) => CallExternal(name, args.map(f))
        MakeTuple(arr) => MakeTuple(arr.map(f))
        LetTuple(arr, val, w) => LetTuple(arr.map(f), f(val), rename(w, f))
        PackClosure(ff) => PackClosure(f(ff))
        Deref(ptr) => Deref(f(ptr))
        Save(ptr, val) => Save(f(ptr), f(val))
        LShift(x, i) => LShift(f(x), i)
        t => t
    }
}

fn prepare_alias(expr: Expr) -> Unit {
    match expr {
        Let(a, val, w) => {
            match val {
                Var(x) => {
                    // Never tamper global variables
                    // otherwise tidy() will not work in emit
                    if (glob.val.contains(x).not()) {
                        e.alias[a] = x;
                    }
                }
                _ => ()
            }
            prepare_alias(val);
            prepare_alias(w);
        }
        LetTuple(_, _, w) =>
            prepare_alias(w)
        IfLe(_, _, body, otherwise) |
        IfEq(_, _, body, otherwise) => {
            prepare_alias(body);
            prepare_alias(otherwise);
        }
        _ => ()
    }
}

fn opt_cse_(expr: Expr) -> Expr {
    match expr {
        Let(a, val, w) => {
            let opt = opt_cse_(val);
            if (side_effect_free(val) && no_mutable(val)) {
                match val {
                    Var(_) | Unit | Int(_) | Double(_) => ()
                    _ => {
                        if (e.subexpr.contains(val).not()) {
                            e.subexpr[val] = a;
                        } else {
                            println("spot: \{val} <= \{e.subexpr[val].unwrap()}")
                            e.alias[a] = e.subexpr[val].unwrap();
                        }
                    }
                };
                Let(a, opt, opt_cse_(w))
            } else {
                Let(a, val, opt_cse_(w))
            }
        }
        LetTuple(x, arr, w) =>
            LetTuple(x, arr, opt_cse_(w))
        // Need some careful handling of if-else though
        // not sure
        t => t
    }
}

/// Common subexpression elimination
pub fn opt_cse(program: Program) -> Program {
    fn do_alias(x) {
        match e.alias[x] {
            Some(t) => t
            None => x
        }
    }
    for x in program.fundefs {
        e.subexpr.clear();
        e.alias.clear();

        prepare_alias(x.body);
        x.body = rename(x.body, do_alias);
        x.body = rename(opt_cse_(x.body), do_alias);
    }
    println(program.body)
    return program;
}