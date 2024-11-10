pub struct OptEnv {
    // All names used in the program
    mut used_names: @immut/hashset.T[Name]

    // Subexpressions that might be eliminable
    mut subexpr: Map[Expr, Name]

    // Two names refer to the same thing
    mut alias: Map[Name, Name]

    // All transformed (un-closured) functions
    mut transformed: @immut/hashset.T[Name]
}

let e: OptEnv = OptEnv :: {
    used_names: @immut/hashset.T::new(),
    subexpr: Map::new(),
    alias: Map::new(),
    transformed: @immut/hashset.T::new(),
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

        Unit | Int(_) | Double(_) | ExternalArray(_) =>
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
            ["minimbt_read_int", "minimbt_read_char", "minimbt_print_int", "minimbt_print_char",
            "minimbt_print_endline", "minimbt_malloc", "minimbt_create_ptr_array",
            "minimbt_create_float_array", "minimbt_create_array"].contains(name._).not()
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

// This is for opt_remove_closure
fn prepare_closure_alias(expr: Expr) -> Unit {
    match expr {
        Let(a, val, w) => {
            match val {
                PackClosure(x) => 
                    e.alias[a] = x;
                
                _ => ()
            }
            prepare_closure_alias(val);
            prepare_closure_alias(w);
        }
        LetTuple(_, _, w) =>
            prepare_closure_alias(w)
        IfLe(_, _, body, otherwise) |
        IfEq(_, _, body, otherwise) => {
            prepare_closure_alias(body);
            prepare_closure_alias(otherwise);
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
        IfEq(a, b, body, otherwise) => {
            // We can't cross boundary of branches
            let s = e.subexpr;
            let al = e.alias;
            let left = opt_cse_one(body);
            e.subexpr = s;
            e.alias = al;

            let s = e.subexpr;
            let al = e.alias;
            let right = opt_cse_one(otherwise);
            e.subexpr = s;
            e.alias = al;
            IfEq(a, b, left, right);
        }
        IfLe(a, b, body, otherwise) => {
            let s = e.subexpr;
            let al = e.alias;
            let left = opt_cse_one(body);
            e.subexpr = s;
            e.alias = al;

            let s = e.subexpr;
            let al = e.alias;
            let right = opt_cse_one(otherwise);
            e.subexpr = s;
            e.alias = al;
            IfLe(a, b, left, right);
        }
        t => t
    }
}

fn opt_cse_one(expr: Expr) -> Expr {
    fn do_alias(x) {
        match e.alias[x] {
            Some(t) => t
            None => x
        }
    }

    e.subexpr.clear();
    e.alias.clear();

    prepare_alias(expr);
    let renamed = rename(expr, do_alias);
    return rename(opt_cse_(renamed), do_alias);
}

/// Common subexpression elimination
pub fn opt_cse(program: Program) -> Program {
    for x in program.fundefs {
        x.body = opt_cse_one(x.body);
    }
    return program;
}

fn type_of(x: Name) -> @types.Type {
    match @knf.typing[x] {
        Some(t) => t
        None => @util.die("closure: cannot identify type: \{x}")
    }
}

fn reform(expr: Expr) -> Expr {
    fn transformed(x) {
        if (e.transformed.contains(x)) {
            return true;
        }
        if (e.alias.contains(x)) {
            return e.transformed.contains(e.alias[x].unwrap());
        }
        return false;
    }

    fn captured(x) {
        if (e.transformed.contains(x)) {
            return find_function(x).unwrap().captured;
        }
        if (e.alias.contains(x)) {
            return find_function(e.alias[x].unwrap()).unwrap().captured;
        }
        @util.die("opt-closure: closure removal corrupted");
    }

    fn real(x) {
        if (e.transformed.contains(x)) {
            return x;
        }
        if (e.alias.contains(x)) {
            return find_function(e.alias[x].unwrap()).unwrap().old_name;
        }
        @util.die("opt-closure: closure removal corrupted");
    }

    match expr {
        Let(a, val, w) => 
            Let(a, reform(val), reform(w))
        LetTuple(x, arr, w) =>
            LetTuple(x, arr, reform(w))
        IfLe(a, b, body, otherwise) =>
            IfLe(a, b, reform(body), reform(otherwise))
        IfEq(a, b, body, otherwise) =>
            IfEq(a, b, reform(body), reform(otherwise))
        Call(f, args) => {
            if (transformed(f)) {
                Call(real(f), args + captured(f));
            } else {
                Call(f, args)
            }
        }
        CallTailRec(f, args) => {
            if (transformed(f)) {
                CallTailRec(real(f), args + captured(f));
            } else {
                CallTailRec(f, args)
            }
        }
        CallClosure(f, args) => {
            if (transformed(f)) {
                Call(real(f), args + captured(f));
            } else {
                CallClosure(f, args)
            }
        }
        t => t
    }
}

fn check_noflee(expr: Expr) -> Bool {
    match expr {
        Let(a, val, w) =>
            check_noflee(val) && check_noflee(w) && match @knf.typing[a] {
                Some(Fun(_)) => false
                Some(Array(Fun(_))) => false
                Some(Array(Array(Fun(_)))) => false
                // Indeed all arrays of functions are not good, but I'm lazy to reform into recursion
                _ => true
            }
        LetTuple(arr, _, w) =>
            arr.fold(~init = true, fn (total, x) { total && is_function(x).not() }) && check_noflee(w)
        IfEq(_, _, body, otherwise) | IfLe(_, _, body, otherwise) =>
            check_noflee(body) && check_noflee(otherwise)
        _ => true
    }
}

fn check_eligibility(x: FuncDef) -> Bool {
    let f_name = x.old_name;

    // global functions can't be closure
    if (t.inside.contains(f_name).not()) {
        return true;
    }

    let mut father_able = true;
    let father = t.inside[f_name].unwrap();

    if (t.inside.contains(father)) {
        father_able = check_eligibility(find_function(father).unwrap());
    }

    let no_flee =
        match type_of(father) {
            Fun(_, Fun(_)) => false
            _ => true
        }

    let no_fn_arg =
        x.captured.fold(~init = true, fn (total, x) { total && match @knf.typing[x] {
            Some(Fun(_)) => false
            _ => true
        } });

    let result = no_flee && no_fn_arg && father_able && check_noflee(x.body) && 
            x.args.length() + x.captured.length() <= 8;
    return result;
}

/// Makes closure into normal functions, whenever possible
pub fn opt_remove_closure(program: Program) -> Program {
    e.transformed = @immut/hashset.T::new();

    for x in program.fundefs {
        if (check_eligibility(x)) {
            x.is_closure = false;
            e.transformed = e.transformed.add(x.old_name);
        }
    }

    for x in program.fundefs {
        e.alias.clear();
        prepare_closure_alias(x.body);
        x.body = reform(x.body);
    }

    for x in e.transformed {
        let x = find_function(x).unwrap();
        x.args += x.captured;
        x.captured = [];
        println("opt-closure: un-closured \{x.old_name}")
    }

    return program;
}