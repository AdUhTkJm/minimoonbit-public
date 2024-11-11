pub struct OptEnv {
    // All names used in the program
    mut used_names: @immut/hashset.T[Name]

    // Records if each function is side-effect free
    mut is_se_free: Map[Name, Bool]

    // Records if each function is weak side-effect free
    mut wse_free: Map[Name, Bool]

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


fn captured(knf: Knf) -> Set {
    match knf {
        Int(_) | Double(_) | Unit | ExternalArray(_) | ConstTuple(_) => Set::new()

        Put(a, b, c) =>
            Set::from_array([a, b, c])

        Add(a, b) | Sub(a, b) | Mul(a, b) | Div(a, b) |
        FAdd(a, b) | FSub(a, b) | FMul(a, b) | FDiv(a, b) |
        Eq(a, b) | Le(a, b) | Get(a, b) => 
            Set::from_array([a, b])

        Neg(a) | BNeg(a) | FNeg(a) => 
            Set::from_array([a])

        ExternalFunctionApplication(_, args) => Set::from_array(args)
        Apply(f, args) | CallTailRec(f, args) => Set::from_array([f, ..args])
        Tuple(arr) => Set::from_array(arr)

        IfEq(a, b, l, r) | IfLe(a, b, l, r) => {
            let mut z = union(captured(l), captured(r));
            z = z.add(a).add(b);
            z
        }
        
        Var(a) => {
            let ff = e.fundef[a];
            if (ff.is_empty()) {
                Set::from_array([a])
            } else {
                Set::from_array([a, ..e.capture[ff.unwrap().name].or([])]);
            }
        }

        Let(x, val, w) => {
            union(captured(val), captured(w)).remove(x)
        }
        LetRec({ name: f_name, ty: _, args: args, body: syn }, w) => {
            let mut z = captured(syn);
            for y in args {
                z = z.remove(y);
            }
            union(captured(w), z).remove(f_name);
        }
        LetTuple(arr, n, w) => {
            let mut z = captured(w);
            for y in arr {
                z = z.remove(y);
            }
            z.add(n);
        }
    }
}


fn OptEnv::new() -> OptEnv {
    let env = OptEnv :: { 
        used_names: @immut/hashset.T::new(),
        is_se_free: Map::new(),
        wse_free: Map::new(),
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
        Let(a, _, c) => union(Set::from_array([a]), globals(c))
        LetRec({ name: f_name, .. }, w) => union(Set::from_array([f_name]), globals(w))
        _ => Set::new();
    }
}

pub fn global_vars(e: Knf) -> Set {
    match e {
        Let(a, _, c) => union(Set::from_array([a]), global_vars(c))
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
        IfEq(_, _, body, otherwise) | IfLe(_, _, body, otherwise) =>
            side_effect_free(body) && side_effect_free(otherwise)
        Let(_, val, w) =>
            side_effect_free(val) && side_effect_free(w)
        LetTuple(_, _, w) =>
            side_effect_free(w)
        Put(_) => false
        Var(x) => e.is_se_free[x] != Some(false)
        Apply(x, _) => e.is_se_free[x] != Some(false)
        _ => true
    }
}

fn weak_side_effect_free(knf: Knf) -> Bool {
    match knf {
        LetRec({ name: name, body: syn, .. }, w) => {
            if (e.wse_free.contains(name).not()) {
                e.wse_free[name] = true;
                e.wse_free[name] = weak_side_effect_free(syn);
            }
            weak_side_effect_free(w);
        }
        ExternalFunctionApplication(name, _) =>
            ["minimbt_read_int", "minimbt_read_char", "minimbt_print_int", "minimbt_print_char",
            "minimbt_print_endline"].contains(name).not()
        IfEq(_, _, body, otherwise) | IfLe(_, _, body, otherwise) =>
            weak_side_effect_free(body) && weak_side_effect_free(otherwise)
        Let(_, val, w) =>
            weak_side_effect_free(val) && weak_side_effect_free(w)
        LetTuple(_, _, w) =>
            weak_side_effect_free(w)
        Var(x) => e.wse_free[x] != Some(false)
        Apply(x, _) => e.wse_free[x] != Some(false)
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
        IfEq(_, _, body, otherwise) | IfLe(_, _, body, otherwise) => {
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
            if (used(name).not() && name.name.unwrap().starts_with("init_").not()) {
                opt_remove_unused_(w)
            } else {
                LetRec({ name: name, ty: ty, args: args, body: opt_remove_unused_(syn) }, opt_remove_unused_(w))
            }
        IfLe(a, b, body, otherwise) =>
            IfLe(a, b, opt_remove_unused_(body), opt_remove_unused_(otherwise))
        IfEq(a, b, body, otherwise) =>
            IfEq(a, b, opt_remove_unused_(body), opt_remove_unused_(otherwise))
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
        IfLe(a, b, body, otherwise) | IfEq(a, b, body, otherwise) => {
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

struct Emulator {
    // Used when trying to interpret KNF
    mut local: Map[Name, Constant]
}

pub fn Emulator::new() -> Emulator {
    let emu = Emulator :: {
        local: Map::new(),
    };
    for k, _ in e.fundef {
        emu.local[k] = Closure(k, []);
    }
    return emu;
}

pub fn Emulator::find(self: Emulator, x: Name) -> Constant {
    match self.local[x] {
        Some(v) => delete_refer(v)
        None => Unknown
    }
}

pub fn Emulator::emulate(self: Emulator, knf: Knf, depth: Int) -> Constant {
    if (depth > 400) {
        return Unknown;
    }
    let mut result: Constant = Unit;
    let mut current = knf;
    while (result != Unknown) {
    if (e.counter > 5000000) {
        e.proceed = false;
        return Unknown;
    }
    e.counter += 1;
    result = match current {
        Unit => Unit
        Int(i) => Int(i)
        Double(d) => Double(d)
        Var(v) => self.find(v)
        Neg(x) => {
            match self.find(x) {
                Int(x) => Int(-x)
                _ => return Unknown
            }
        }
        BNeg(x) => {
            match self.find(x) {
                Int(1) => Int(0)
                Int(0) => Int(1)
                _ => return Unknown
            }
        }
        Add(x, y) => {
            match (self.find(x), self.find(y)) {
                (Int(x), Int(y)) => Int(x + y)
                _ => return Unknown
            }
        }
        Sub(x, y) => {
            match (self.find(x), self.find(y)) {
                (Int(x), Int(y)) => Int(x - y)
                _ => return Unknown
            }
        }
        Mul(x, y) => {
            match (self.find(x), self.find(y)) {
                (Int(x), Int(y)) => Int(x * y)
                _ => return Unknown
            }
        }
        Div(x, y) => {
            match (self.find(x), self.find(y)) {
                (Int(x), Int(y)) => Int(x / y)
                _ => return Unknown
            }
        }
        Eq(x, y) => {
            match (self.find(x), self.find(y)) {
                (Int(x), Int(y)) => Int(if (x == y) {1} else {0})
                (Double(x), Double(y)) => Int(if (x == y) {1} else {0})
                _ => return Unknown
            }
        }
        Le(x, y) => {
            match (self.find(x), self.find(y)) {
                (Int(x), Int(y)) => Int(if (x <= y) {1} else {0})
                (Double(x), Double(y)) => Int(if (x <= y) {1} else {0})
                _ => return Unknown
            }
        }
        FNeg(x) => {
            match self.find(x) {
                Double(x) => Double(-x)
                _ => return Unknown
            }
        }
        FAdd(x, y) => {
            match (self.find(x), self.find(y)) {
                (Double(x), Double(y)) => Double(x + y)
                _ => return Unknown
            }
        }
        FSub(x, y) => {
            match (self.find(x), self.find(y)) {
                (Double(x), Double(y)) => Double(x - y)
                _ => return Unknown
            }
        }
        FMul(x, y) => {
            match (self.find(x), self.find(y)) {
                (Double(x), Double(y)) => Double(x * y)
                _ => return Unknown
            }
        }
        FDiv(x, y) => {
            match (self.find(x), self.find(y)) {
                (Double(x), Double(y)) => Double(x / y)
                _ => return Unknown
            }
        }
        IfEq(x, y, body, otherwise) => {
            let const = self.emulate(Eq(x, y), depth + 1);
            match const {
                Int(1) => {
                    current = body;
                    continue;
                }
                Int(0) => {
                    current = otherwise;
                    continue;
                }
                _ => return Unknown
            }
        }
        IfLe(x, y, body, otherwise) => {
            let const = self.emulate(Le(x, y), depth + 1);
            match const {
                Int(1) => {
                    current = body;
                    continue;
                }
                Int(0) => {
                    current = otherwise;
                    continue;
                }
                _ => return Unknown
            }
        }
        Let(x, val, w) => {
            self.local[x] = self.emulate(val, depth + 1);
            current = w;
            continue;
        }
        LetRec({ name: f_name, .. }, w) => {
            self.local[f_name] = Closure(f_name, e.capture[f_name].unwrap().map(fn (x) { self.find(x) }));
            current = w;
            continue;
        }
        Apply(f, args) => {
            let f = self.find(f);
            match f {
                Closure(name, earg) => {
                    let env = {
                        local: Map::from_iter(self.local.iter()),
                    };

                    if (e.fundef.contains(name).not()) {
                        @util.die("opt-knf: cannot call \{name}")
                    }

                    let fdef = e.fundef[name].unwrap();
                    let _ = args.mapi(fn (i, x) {
                        env.local[fdef.args[i]] = self.find(x);
                    });

                    let captured = e.capture[name].unwrap();
                    let _ = earg.mapi(fn (i, x) {
                        env.local[captured[i]] = x;
                    });

                    if (known(Tuple(args.map(fn (x) { self.find(x) })))) {
                        env.emulate(fdef.body, depth + 1);
                    } else {
                        return Unknown
                    }
                }
                _ => return Unknown
            }
        }
        CallTailRec(f, args) => {
            let f = self.find(f);
            match f {
                Closure(name, _) => {
                    if (e.fundef.contains(name).not()) {
                        @util.die("opt-knf: cannot call \{name}")
                    }

                    let fdef = e.fundef[name].unwrap();
                    let _ = args.mapi(fn (i, x) {
                        self.local[fdef.args[i]] = self.find(x);
                    });

                    if (known(Tuple(args.map(fn (x) { self.find(x) })))) {
                        current = fdef.body;
                        continue; // while (true)
                    } else {
                        return Unknown
                    }
                }
                _ => return Unknown
            }
        }
        Tuple(arr) => {
            Tuple(arr.map(fn (x) { self.find(x) }))
        }
        LetTuple(arr, val, w) => {
            match self.find(val) {
                Tuple(v) => {
                    let _ = arr.mapi(fn (i, x) {
                        self.local[x] = v[i];
                    });
                }
                _ => return Unknown
            }
            self.emulate(w, depth + 1)
        }
        Get(x, i) => {
            match (self.find(x), self.find(i)) {
                (ValuefulArray(v), Int(i)) => v[i]
                _ => return Unknown
            }
        }
        Put(x, i, val) => {
            match (self.find(x), self.find(i)) {
                (ValuefulArray(v), Int(i)) => {
                    v[i] = self.find(val);
                }
                _ => ()
            }
            Unit
        }
        ConstTuple(x) => Tuple(x)
        ExternalArray(x) => ValuefulArray(x)
        ExternalFunctionApplication(name, args) => {
            match name {
                "minimbt_read_int" | "minimbt_read_char" =>
                    return Unknown

                "minimbt_print_int" | "minimbt_print_endline" |
                "minimbt_print_char" =>
                    Unit

                "minimbt_sin" => {
                    match self.find(args[0]) {
                        Double(x) => Double(@math.sin(x))
                        _ => return Unknown
                    }
                }

                "minimbt_cos" => {
                    match self.find(args[0]) {
                        Double(x) => Double(@math.cos(x))
                        _ => return Unknown
                    }
                }

                "minimbt_atan" => {
                    match self.find(args[0]) {
                        Double(x) => Double(@math.atan(x))
                        _ => return Unknown
                    }
                }

                "minimbt_sqrt" => {
                    match self.find(args[0]) {
                        Double(x) => Double(x.sqrt())
                        _ => return Unknown
                    }
                }

                "minimbt_floor" => {
                    match self.find(args[0]) {
                        Double(x) => Double(x.floor())
                        _ => return Unknown
                    }
                }

                "minimbt_abs_float" => {
                    match self.find(args[0]) {
                        Double(x) => Double(if (x < 0) { -x } else { x })
                        _ => return Unknown
                    }
                }

                "minimbt_int_of_float" | "minimbt_truncate" => {
                    match self.find(args[0]) {
                        Double(x) => Int(x.to_int())
                        _ => return Unknown
                    }
                }

                "minimbt_float_of_int" => {
                    match self.find(args[0]) {
                        Int(x) => Double(x.to_double())
                        _ => return Unknown
                    }
                }

                "minimbt_create_array" => {
                    match (self.find(args[0]), self.find(args[1])) {
                        (Int(len), Int(elem)) => ValuefulArray(Array::make(len, Int(elem)));
                        _ => return Unknown
                    }
                }

                "minimbt_create_ptr_array" => {
                    match (self.find(args[0]), self.find(args[1])) {
                        (Int(len), Fun(f)) => ValuefulArray(Array::make(len, Fun(f)));
                        (Int(len), ValuefulArray(arr)) => ValuefulArray(Array::make(len, ValuefulArray(arr)));
                        _ => return Unknown
                    }
                }

                "minimbt_create_float_array" => {
                    match (self.find(args[0]), self.find(args[1])) {
                        (Int(len), Double(elem)) => ValuefulArray(Array::make(len, Double(elem)));
                        _ => return Unknown
                    }
                }

                _ => @util.die("opt-knf: unknown external function \{name}")
            }
        }
    }
    break; // while (true)
    }
    return result;
}

fn known(x: Constant) -> Bool {
    match delete_refer(x) {
        Int(_) | Double(_) | Unit | Fun(_) => true

        Tuple(x) | ValuefulArray(x) | Closure(_, x)
            => x.fold(~init = true, fn (total, x) { total && known(x) });
        
        Unknown => false

        Refer(_) => @util.die("opt-knf: refer should have been deleted")
    }
}

fn closured(x: Constant) -> Bool {
    match delete_refer(x) {
        Int(_) | Double(_) | Unit => false

        Tuple(x) | ValuefulArray(x) => x.fold(~init = false, fn (total, x) { total || closured(x) });
        
        Fun(_) | Closure(_) | Unknown => true

        Refer(_) => @util.die("opt-knf: refer should have been deleted")
    }
}

fn replace(knf: Knf, env: Emulator) -> Knf {
    match knf {
        Let(a, val, w) => {
            if (weak_side_effect_free(val).not()) {
                return Let(a, replace(val, env), replace(w, env));
            }
            if (env.local.contains(a).not()) {
                return Let(a, replace(val, env), replace(w, env));
            }
            
            match delete_refer(env.local[a].unwrap()) {
                Unit =>
                    Let(a, Unit, replace(w, env));

                Int(x) =>
                    Let(a, Int(x), replace(w, env));

                Double(x) =>
                    Let(a, Double(x), replace(w, env));
                
                Tuple(x) as v =>
                    if (known(v) && closured(v).not()) {
                        Let(a, ConstTuple(x), replace(w, env));
                    } else {
                        Let(a, replace(val, env), replace(w, env))
                    }

                ValuefulArray(x) as v =>
                    if (known(v) && closured(v).not()) {
                        Let(a, ExternalArray(x), replace(w, env));
                    } else {
                        Let(a, replace(val, env), replace(w, env))
                    }

                Unknown | Fun(_) | Closure(_) => Let(a, replace(val, env), replace(w, env))

                Refer(_) => @util.die("opt-knf: refer should have been deleted")
            }
        }

        LetTuple(arr, val, w) => {
            if (env.local.contains(val).not()) {
                @util.die("opt-knf: unknown name in replacement: \{val}")
            }
            match delete_refer(env.local[val].unwrap()) {
                Tuple(y) as v => {
                    if (known(v)) {
                        arr.foldi(~init = replace(w, env), fn (i, total, a) {
                            match delete_refer(y[i]) {
                                Unit =>
                                    Let(a, Unit, total);

                                Int(x) =>
                                    Let(a, Int(x), total);

                                Double(x) =>
                                    Let(a, Double(x), total);
                                
                                Tuple(x) =>
                                    Let(a, ConstTuple(x), total);

                                ValuefulArray(x) =>
                                    Let(a, ExternalArray(x), total);

                                Fun(f) | Closure(f, _) => Let(a, Var(f), replace(w, env))

                                Refer(_) => @util.die("opt-knf: refer should have been deleted")

                                Unknown => @util.die("opt-knf: known() failed")
                            }
                        });
                    } else {
                        LetTuple(arr, val, replace(w, env));
                    }
                }
                Unknown => LetTuple(arr, val, replace(w, env));
                t => @util.die("opt-knf: expected tuple: \{val} (= \{t})")
            }
        }

        LetRec(f, w) =>
            LetRec(f, replace(w, env));
        
        IfEq(a, b, body, otherwise) =>
            IfEq(a, b, replace(body, env), replace(otherwise, env));

        IfLe(a, b, body, otherwise) =>
            IfLe(a, b, replace(body, env), replace(otherwise, env));
        
        t => t
    }
}

fn eliminate_main_call(knf: Knf) -> Knf {
    match knf {
        Let(_, _, w) => eliminate_main_call(w)
        LetRec(_, w) => eliminate_main_call(w)
        _ => Unit
    }
}

fn modify_main(knf: Knf, body: Knf) -> Knf {
    match knf {
        Let(a, val, w) =>
            Let(a, val, modify_main(w, body))
        LetRec({ name: name, .. } as def, w) => {
            if (name.name == Some("main")) {
                LetRec({ name: name, ty: Fun([], Unit), args: [], body: body }, w);
            } else {
                LetRec(def, modify_main(w, body));
            }
        }
        t => t
    }
}

fn gather_capture(knf: Knf) -> Unit {
    match knf {
        Let(_, val, w) => {
            gather_capture(val);
            gather_capture(w);
        }
        LetTuple(_, _, w) => {
            gather_capture(w);
        }
        LetRec({ name: f_name, body: syn, args: args, .. }, w) => {
            let mut caps = captured(syn);
            for x in args {
                caps = caps.remove(x);
            }
            for x in e.global {
                caps = caps.remove(x);
            }
            e.capture[f_name] = Array::from_iter(caps.remove(f_name).iter());
            gather_capture(syn);
            gather_capture(w);
        }
        IfEq(_, _, body, otherwise) | IfLe(_, _, body, otherwise) => {
            gather_capture(body);
            gather_capture(otherwise);
        }
        _ => ()
    }
}

pub fn opt_emulate(knf: Knf) -> Knf {
    let env = Emulator::new();
    let result = env.emulate(eliminate_main_call(knf), 0);
    if (result == Unknown) {
        return knf;
    }
    
    // To reflect the CallTailRec back on our KNF
    e.fundef.clear();
    prepare_fundef(knf);

    e.global = globals(knf);
    for i = 0; i < 5; i = i + 1 {
        gather_capture(knf);
    }

    for k, v in e.fundef {
        if (k.name == Some("main")) {
            let body = v.body;
            let _ = env.emulate(body, 0);
            if (e.proceed == false) {
                return knf;
            }
            let new = replace(body, env);
            e.fundef[k] = {
                ..e.fundef[k].unwrap(),
                body: new
            };
            return modify_main(knf, new);
        }
    }
    return knf;
}

pub fn opt_remove_unreachable(knf: Knf) -> Knf {
    if (e.proceed == false) {
        return knf;
    }

    // Disable this, when we have init()
    for k, _ in e.fundef {
        if (k.name.unwrap().starts_with("init_") &&
            k.name.unwrap().ends_with("_" + k.slot.to_string())) {
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

    for i = 0; i < 5; i = i + 1 {
        for k, v in e.fundef {
            e.is_se_free[k] = side_effect_free(v.body);
            e.wse_free[k] = weak_side_effect_free(v.body);
        }
    }

    let opt = knf
        |> opt_const_fold
        |> opt_remove_unused
        |> opt_tail_rec
        |> opt_emulate
        |> opt_remove_unreachable;
    
    return opt;
}