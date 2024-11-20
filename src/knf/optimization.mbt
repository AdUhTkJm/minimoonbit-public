pub struct OptEnv {
    // All names used in the program
    mut used_names: @immut/hashset.T[Name]

    // Records if each function is side-effect free
    mut is_se_free: Map[Name, Bool]

    // Records function body of each function
    mut fundef: Map[Name, FuncDef]

    // Records the value of each intermediate name
    mut value: Map[Name, Constant]

    // If the tail recursion is successful
    mut tail_success: Perhaps

    // Captured variables of each function
    mut capture: Map[Name, Array[Name]]

    // A list of all global things
    mut global: @immut/hashset.T[Name]

    // How long we've spent in emulation
    mut counter: Int

    // Shall we proceed in opt_emulate
    mut proceed: Bool
}

pub enum Constant {
    Unit
    Int(Int)
    Double(Double)
    Fun(Name)
    Closure(Name, Array[Constant])
    Refer(Name)
    ValuefulArray(Array[Constant])
    Tuple(Array[Constant])
    Unknown
} derive(Show)

pub enum Perhaps {
    Yes
    No
    Maybe
    Unknown
} derive(Show, Eq)

pub fn Constant::op_equal(self: Constant, other: Constant) -> Bool {
    match (self, other) {
        (Refer(x), a) | (a, Refer(x)) => match e.value[x] {
            Some(t) => t == a
            None => false
        }
        (Int(x), Int(y)) => x == y
        (Double(x), Double(y)) => x == y
        (Fun(x), Fun(y)) => x == y
        (Unit, Unit) => true
        _ => false
    }
}


fn OptEnv::new() -> OptEnv {
    let env = OptEnv :: { 
        used_names: @immut/hashset.T::new(),
        is_se_free: Map::new(),
        fundef: Map::new(),
        value: Map::new(),
        capture: Map::new(),
        tail_success: Unknown,
        global: @immut/hashset.T::new(),
        counter: 0,
        proceed: true
    }
    return env;
}

fn union(a: @immut/hashset.T[@types.Name], b: @immut/hashset.T[@types.Name]) -> @immut/hashset.T[@types.Name] {
    let mut l = a;
    for z in b {
        l = l.add(z);
    }
    l;
}

fn union_names(a: @immut/hashset.T[(String, @types.Type)], b: @immut/hashset.T[(String, @types.Type)]) -> @immut/hashset.T[(String, @types.Type)] {
    let mut l = a;
    for z in b {
        l = l.add(z);
    }
    l;
}

typealias Set = @immut/hashset.T[Name];

pub fn globals(e: Knf) -> Set {
    match e {
        Let(a, _, w) => union(Set::from_array([a]), globals(w))
        LetRec({ name: f_name, .. }, w) => union(Set::from_array([f_name]), globals(w))
        _ => Set::new();
    }
}

pub fn global_vars(e: Knf) -> Set {
    match e {
        Let(a, _, w) => union(Set::from_array([a]), global_vars(w))
        LetRec(_, w) => global_vars(w)
        _ => Set::new();
    }
}

fn OptEnv::add_used(self: OptEnv, arr: Array[Name]) -> Unit {
    self.used_names = union(self.used_names, @immut/hashset.T::from_array(arr));
}

pub fn delete_refer(x: Constant) -> Constant {
    match x { 
        Refer(x) => match e.value[x] {
            Some(z) => delete_refer(z)
            None => Unknown
        }
        t => t
    }
}

pub fn value_of(name: Name) -> Constant {
    match e.value[name] {
        Some(x) => {
            let d = delete_refer(x);
            e.value[name] = d;
            d
        }
        None => Unknown
    }
}

pub let e: OptEnv = OptEnv::new();


fn get_used(knf: Knf) -> Unit {
    match knf {
        Add(a, b) | Sub(a, b) | Mul(a, b) | Div(a, b) |
        FAdd(a, b) | FSub(a, b) | FMul(a, b) | FDiv(a, b) |
        Eq(a, b) | Le(a, b) | Get(a, b) =>
            e.add_used([a, b]);

        Neg(a) | BNeg(a) | FNeg(a) | Var(a) =>
            e.add_used([a]);

        Unit | Int(_) | Double(_) | ConstTuple(_) | ExternalArray(_) =>
            ();

        IfEq(a, b, body, otherwise) |
        IfLe(a, b, body, otherwise) |
        IfNe(a, b, body, otherwise) => {
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

        LetRec({ body: syn, args: args, .. }, w) => {
            e.add_used(args);
            get_used(syn);
            get_used(w);
        }

        Apply(a, arr) | CallTailRec(a, arr) =>
            e.add_used([..arr, a]);

        Tuple(arr) | ExternalFunctionApplication(_, arr) =>
            e.add_used(arr);

        Put(x, i, val) =>
            e.add_used([x, i, val]);

        Match(a, branches) => {
            e.add_used([a]);
            for x in branches {
                get_used(x.exec);
            }
        }
    }
}

fn side_effect_free(knf: Knf) -> Bool {
    match knf {
        LetRec({ name: name, body: syn, .. }, w) => {
            // This line is to prevent infinite recursion
            // Consider f() { f(); }
            if (e.is_se_free.contains(name).not()) {
                e.is_se_free[name] = true;
                e.is_se_free[name] = side_effect_free(syn);
            }
            side_effect_free(w);
        }
        ExternalFunctionApplication(name, _) =>
            ["minimbt_read_int", "minimbt_read_char", "minimbt_print_int", "minimbt_print_char",
            "minimbt_print_endline", "minimbt_malloc", "minimbt_create_ptr_array",
            "minimbt_create_array", "minimbt_create_float_array"].contains(name).not()
        IfEq(_, _, body, otherwise) | IfLe(_, _, body, otherwise) | IfNe(_, _, body, otherwise) =>
            side_effect_free(body) && side_effect_free(otherwise)
        Let(_, val, w) =>
            side_effect_free(val) && side_effect_free(w)
        LetTuple(_, _, w) =>
            side_effect_free(w)
        Put(_) => false
        Var(x) | Apply(x, _) => {
            match typing[x] {
                Some(Fun(_)) => {
                    if (e.value.contains(x)) {
                        match value_of(x) {
                            Fun(v) => 
                                e.is_se_free[v].unwrap();
                            
                            _ => false
                        }
                    } else { false }
                }
                _ => true
            }
        }
        _ => true
    }
}

fn prepare_fundef(knf: Knf) -> Unit {
    match knf {
        LetRec({ name: name, body: syn, .. } as def, w) => {
            e.fundef[name] = def;
            e.value[name] = Fun(name);
            prepare_fundef(syn);
            prepare_fundef(w);
        }
        IfEq(_, _, body, otherwise) | IfLe(_, _, body, otherwise) | IfNe(_, _, body, otherwise) => {
            prepare_fundef(body);
            prepare_fundef(otherwise)
        }
        Let(_, val, w) => {
            prepare_fundef(val);
            prepare_fundef(w);
        }
        LetTuple(_, _, w) =>
            prepare_fundef(w)
        _ => ()
    }
}

fn used(name: Name) -> Bool {
    return e.used_names.contains(name);
}

fn is_init(name: Name) -> Bool {
    match name.name {
        Some(n) => n.starts_with("init_") &&
            n.ends_with("_" + name.slot.to_string());
        None => false
    }
}

// Removes all unused instances of a variable
fn opt_remove_unused_(knf: Knf) -> Knf {
    match knf {
        Let(a, val, w) => {
            if (used(a).not() && side_effect_free(val)) {
                opt_remove_unused_(w);
            } else {
                Let(a, opt_remove_unused_(val), opt_remove_unused_(w));
            }
        }
        LetTuple(x, arr, w) =>
            LetTuple(x, arr, opt_remove_unused_(w))
        LetRec({ name: name, ty: ty, args: args, body: syn }, w) =>
            if (used(name).not() && is_init(name).not()) {
                opt_remove_unused_(w)
            } else {
                LetRec({ name: name, ty: ty, args: args, body: opt_remove_unused_(syn) }, opt_remove_unused_(w))
            }
        IfLe(a, b, body, otherwise) =>
            IfLe(a, b, opt_remove_unused_(body), opt_remove_unused_(otherwise))
        IfEq(a, b, body, otherwise) =>
            IfEq(a, b, opt_remove_unused_(body), opt_remove_unused_(otherwise))
        IfNe(a, b, body, otherwise) =>
            IfNe(a, b, opt_remove_unused_(body), opt_remove_unused_(otherwise))
        Match(a, branches) => {
            for x in branches {
                x.exec = opt_remove_unused_(x.exec);
            }
            Match(a, branches)
        }
        t => t
    }
}

pub fn opt_remove_unused(knf: Knf) -> Knf {
    e.used_names = @immut/hashset.T::new();
    get_used(knf);
    opt_remove_unused_(knf);
}

/// Do basic constant folding;
/// This stage stores values that can be used by @closure
pub fn opt_const_fold(knf: Knf) -> Knf {
    match knf {
        Let(a, val, w) => {
            let k = val |> opt_const_fold |> opt_remove_unused;

            e.value[a] = match k {
                Var(x) => Refer(x);
                Int(x) => Int(x);
                Double(x) => Double(x);
                Unit => Unit;
                _ => Unknown;
            }
            Let(a, k, opt_const_fold(w));
        }
        LetTuple(arr, x, w) =>
            LetTuple(arr, x, opt_const_fold(w))
        LetRec({ name: name, ty: ty, args: args, body: syn }, w) => {
            LetRec({ name: name, ty: ty, args: args, body: opt_const_fold(syn) }, opt_const_fold(w))
        }
        IfLe(a, b, body, otherwise) =>
            IfLe(a, b, opt_const_fold(body), opt_const_fold(otherwise))
        IfEq(a, b, body, otherwise) =>
            IfEq(a, b, opt_const_fold(body), opt_const_fold(otherwise))
        IfNe(a, b, body, otherwise) =>
            IfNe(a, b, opt_const_fold(body), opt_const_fold(otherwise))
        Match(a, branches) => {
            for x in branches {
                x.exec = opt_const_fold(x.exec)
            }
            Match(a, branches)
        }
        Add(a, b) => {
            match (value_of(a), value_of(b)) {
                ((Int(x)), (Int(y))) => Int(x + y)
                _ => Add(a, b)
            }
        }
        Sub(a, b) => {
            match (value_of(a), value_of(b)) {
                ((Int(x)), (Int(y))) => Int(x - y)
                _ => Sub(a, b)
            }
        }
        Mul(a, b) => {
            match (value_of(a), value_of(b)) {
                ((Int(x)), (Int(y))) => Int(x * y)
                _ => Mul(a, b)
            }
        }
        Div(a, b) => {
            match (value_of(a), value_of(b)) {
                ((Int(x)), (Int(y))) => Int(x / y)
                _ => Div(a, b)
            }
        }
        Neg(a) => {
            match (value_of(a)) {
                ((Int(x))) => Int(-x)
                _ => Neg(a)
            }
        }
        FAdd(a, b) => {
            match (value_of(a), value_of(b)) {
                ((Double(x)), (Double(y))) => Double(x + y)
                _ => FAdd(a, b)
            }
        }
        FSub(a, b) => {
            match (value_of(a), value_of(b)) {
                ((Double(x)), (Double(y))) => Double(x - y)
                _ => FSub(a, b)
            }
        }
        FMul(a, b) => {
            match (value_of(a), value_of(b)) {
                (Double(x), Double(y)) => Double(x * y)
                _ => FMul(a, b)
            }
        }
        FDiv(a, b) => {
            match (value_of(a), value_of(b)) {
                (Double(x), Double(y)) => Double(x / y)
                _ => FDiv(a, b)
            }
        }
        FNeg(a) => {
            match (value_of(a)) {
                (Double(x)) => Double(-x)
                _ => FNeg(a)
            }
        }
        Var(x) => match value_of(x) {
            Int(x) => Int(x)
            Double(x) => Double(x)
            _ => Var(x)
        }
        t => t
    }
}

fn opt_tail_rec_(knf: Knf, func: @types.Name) -> Knf {
    match knf {
        // We don't want to make intermediate calls in "val" also tail-recursive
        // but if there are functions in "val", we can make them tail-recursive
        // so we still want to call opt_tail_rec_ on it, but giving it (-1)
        Let(a, val, w) =>
            Let(a, opt_tail_rec_(val, Name::slot_only(-1)), opt_tail_rec_(w, func));
        LetTuple(arr, x, w) =>
            LetTuple(arr, x, opt_tail_rec_(w, func))
        LetRec({ name: name, ty: ty, args: args, body: syn }, w) =>
            LetRec({ name: name, ty: ty, args: args, body: opt_tail_rec_(syn, name) }, opt_tail_rec_(w, func))
        IfLe(a, b, body, otherwise) | IfEq(a, b, body, otherwise) | IfNe(a, b, body, otherwise) => {
            let mut left = opt_tail_rec_(body, func);
            if (e.tail_success == No) {
                left = body;
            }
            let mut right = opt_tail_rec_(otherwise, func);
            if (e.tail_success == No) {
                right = otherwise;
            }

            match knf {
                IfLe(_) => IfLe(a, b, left, right);
                IfEq(_) => IfEq(a, b, left, right);
                IfNe(_) => IfNe(a, b, left, right);
                _ => @util.die("opt-tail: impossible")
            }
        }
        Apply(x, args) => {
            if (value_of(x) == Fun(func)) {
                e.tail_success = Maybe;
                CallTailRec(x, args)
            } else {
                if (e.tail_success == Maybe) {
                    e.tail_success = No;
                }
                Apply(x, args)
            }
        }
        Unit | Int(_) | Double(_) | Tuple(_) | Var(_) | Get(_) => {
            e.tail_success = Yes;
            knf
        }
        t => {
            if (e.tail_success == Maybe) {
                e.tail_success = No;
            }

            t
        }
    }
}

pub fn opt_tail_rec(knf: Knf) -> Knf {
    e.tail_success = Unknown;
    opt_tail_rec_(knf, Name::slot_only(-1));
}

pub fn opt_remove_unreachable(knf: Knf) -> Knf {
    // Disable this, when we have init()
    for k, _ in e.fundef {
        if (is_init(k)) {
            return knf;
        }
    }

    for k, v in e.fundef {
        if (k.name == Some("main")) {
            e.used_names = @immut/hashset.T::new().add(k);
            get_used(v.body);

            let mut old_len = -1;
            let mut len = e.used_names.size();

            while (old_len != len) {
                fn update(knf) {
                    match knf {
                        Let(a, val, w) => {
                            if (e.used_names.contains(a)) {
                                get_used(val);
                            }
                            update(w);
                        }
                        LetRec({ name: f_name, body: syn, .. }, w) => {
                            if (e.used_names.contains(f_name)) {
                                get_used(syn);
                            }
                            update(w);
                        }
                        _ => ()
                    }
                }
                update(knf);

                old_len = len;
                len = e.used_names.size();
            }
            break;
        }
    }
    return knf |> opt_remove_unused_;
}

pub fn opt(knf: Knf) -> Knf {
    prepare_fundef(knf);

    for k, _ in e.fundef {
        e.is_se_free[k] = true;
    }

    let mut opt = knf
        |> opt_const_fold;

    // Wait for it to stabilize
    for i = 0; i < 5; i = i + 1 {
        for k, v in e.fundef {
            e.is_se_free[k] = side_effect_free(v.body);
        }
    }

    opt = knf
        |> opt_remove_unused
        |> opt_tail_rec
    
    return opt;
}