pub struct OptEnv {
    // All names used in the program
    mut used_names: @immut/hashset.T[@types.Name]

    // Records if each function is side-effect free
    mut is_se_free: Map[@types.Name, Bool]

    // Records function body of each function
    mut fundef: Map[@types.Name, FuncDef]

    // Records the value of each intermediate name
    mut value: Map[@types.Name, Constant]

    // If the tail recursion is successful
    mut tail_success: Bool
}

pub enum Constant {
    Unit
    Int(Int)
    Double(Double)
    Fun(@types.Name)
    Refer(@types.Name)
    Unknown
} derive(Show)

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
        tail_success: false,
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

fn union_names(a: @immut/hashset.T[String], b: @immut/hashset.T[String]) -> @immut/hashset.T[String] {
    let mut l = a;
    for z in b {
        l = l.add(z);
    }
    l;
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
pub fn value_of(name: Name) -> Option[Constant] {
    match e.value[name] {
        Some(x) => Some(delete_refer(x))
        None => None
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

        LetRec({ body: syn, .. }, w) => {
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
        Apply(_, _) => false     // We know nothing about function content
        ExternalFunctionApplication(name, _) =>
            ["read_int", "read_char", "print_int", "print_char",
            "print_endline", "minimbt_malloc", "minimbt_create_ptr_array"].contains(name)
        IfEq(_, _, body, otherwise) | IfLe(_, _, body, otherwise) =>
            side_effect_free(body) && side_effect_free(otherwise)
        Let(_, val, w) =>
            side_effect_free(val) && side_effect_free(w)
        LetTuple(_, _, w) =>
            side_effect_free(w)
        Put(_) => false
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
            LetRec({ name: name, ty: ty, args: args, body: opt_remove_unused_(syn) }, opt_remove_unused_(w))
        IfLe(a, b, body, otherwise) =>
            IfLe(a, b, opt_remove_unused_(body), opt_remove_unused_(otherwise))
        IfEq(a, b, body, otherwise) =>
            IfEq(a, b, opt_remove_unused_(body), opt_remove_unused_(otherwise))
        t => t
    }
}

pub fn opt_remove_unused(knf: Knf) -> Knf {
    get_used(knf);
    opt_remove_unused_(knf);
}

// Constant folding
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
        LetRec({ name: name, ty: ty, args: args, body: syn }, w) =>
            LetRec({ name: name, ty: ty, args: args, body: opt_const_fold(syn) }, opt_const_fold(w))
        IfLe(a, b, body, otherwise) =>
            IfLe(a, b, opt_const_fold(body), opt_const_fold(otherwise))
        IfEq(a, b, body, otherwise) =>
            IfEq(a, b, opt_const_fold(body), opt_const_fold(otherwise))
        Add(a, b) => {
            match (value_of(a), value_of(b)) {
                (Some(Int(x)), Some(Int(y))) => Int(x + y)
                _ => Add(a, b)
            }
        }
        Sub(a, b) => {
            match (value_of(a), value_of(b)) {
                (Some(Int(x)), Some(Int(y))) => Int(x - y)
                _ => Sub(a, b)
            }
        }
        Mul(a, b) => {
            match (value_of(a), value_of(b)) {
                (Some(Int(x)), Some(Int(y))) => Int(x * y)
                _ => Mul(a, b)
            }
        }
        Div(a, b) => {
            match (value_of(a), value_of(b)) {
                (Some(Int(x)), Some(Int(y))) => Int(x / y)
                _ => Div(a, b)
            }
        }
        Neg(a) => {
            match (value_of(a)) {
                (Some(Int(x))) => Int(-x)
                _ => Neg(a)
            }
        }
        FAdd(a, b) => {
            match (value_of(a), value_of(b)) {
                (Some(Double(x)), Some(Double(y))) => Double(x + y)
                _ => FAdd(a, b)
            }
        }
        FSub(a, b) => {
            match (value_of(a), value_of(b)) {
                (Some(Double(x)), Some(Double(y))) => Double(x - y)
                _ => FSub(a, b)
            }
        }
        FMul(a, b) => {
            match (value_of(a), value_of(b)) {
                (Some(Double(x)), Some(Double(y))) => Double(x * y)
                _ => FMul(a, b)
            }
        }
        FDiv(a, b) => {
            match (value_of(a), value_of(b)) {
                (Some(Double(x)), Some(Double(y))) => Double(x / y)
                _ => FDiv(a, b)
            }
        }
        FNeg(a) => {
            match (value_of(a)) {
                (Some(Double(x))) => Double(-x)
                _ => FNeg(a)
            }
        }
        Var(x) => match value_of(x) {
            Some(Int(x)) => Int(x)
            Some(Double(x)) => Double(x)
            _ => Var(x)
        }
        t => t
    }
}

fn opt_tail_rec_(knf: Knf, func: @types.Name) -> Knf {
    match knf {
        Let(a, val, w) => 
            Let(a, val, opt_tail_rec_(w, func));
        LetTuple(arr, x, w) =>
            LetTuple(arr, x, opt_tail_rec_(w, func))
        LetRec({ name: name, ty: ty, args: args, body: syn }, w) =>
            LetRec({ name: name, ty: ty, args: args, body: opt_tail_rec_(syn, name) }, opt_tail_rec_(w, func))
        IfLe(a, b, body, otherwise) | IfEq(a, b, body, otherwise) => {
            let left = opt_tail_rec_(body, func);
            if (e.tail_success.not()) {
                return knf;
            }
            let right = opt_tail_rec_(otherwise, func);
            if (e.tail_success.not()) {
                return knf;
            }

            match knf {
                IfLe(_) => IfLe(a, b, left, right);
                IfEq(_) => IfLe(a, b, left, right);
                _ => @util.die("Impossible")
            }
        }
        Apply(x, args) => {
            if (e.value[x] == Some(Fun(func))) {
                e.tail_success = true;
                CallTailRec(x, args)
            } else {
                e.tail_success = true;
                Apply(x, args)
            }
        }
        Unit | Int(_) | Double(_) | Tuple(_) | Var(_) => {
            e.tail_success = true;
            knf
        }
        t => {
            e.tail_success = false;
            t
        }
    }
}

pub fn opt_tail_rec(knf: Knf) -> Knf {
    e.tail_success = false;
    opt_tail_rec_(knf, Name::slot_only(-1));
}

pub fn opt(knf: Knf) -> Knf {
    prepare_fundef(knf);
    get_used(knf);

    return knf
    |> opt_const_fold
    |> opt_remove_unused
    // TODO: turn all closure into non-closure
    // |> opt_tail_rec;
}