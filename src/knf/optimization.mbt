pub struct OptEnv {
    // All names used in the program
    mut used_names: @immut/hashset.T[@types.Name]

    // Records if each function is side-effect free
    mut is_se_free: Map[@types.Name, Bool]

    // Records function body of each function
    mut fundef: Map[@types.Name, FuncDef]
}

fn OptEnv::new() -> OptEnv {
    let env = OptEnv :: { 
        used_names: @immut/hashset.T::new(),
        is_se_free: Map::new(),
        fundef: Map::new(),
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
fn OptEnv::add_used(self: OptEnv, arr: Array[Name]) -> Unit {
    self.used_names = union(self.used_names, @immut/hashset.T::from_array(arr));
}

pub let e: OptEnv = OptEnv::new();


fn get_used(knf: Knf) -> Unit {
    match knf {
        Add(a, b) | Sub(a, b) | Mul(a, b) | Div(a, b) |
        FAdd(a, b) | FSub(a, b) | FMul(a, b) | FDiv(a, b) |
        Eq(a, b) | Le(a, b) | Get(a, b) =>
            e.add_used([a, b]);

        Neg(a) | BNeg(a) | FNeg(a) | Var(a) | FVar(a) =>
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

        LetRec({ body: syn, .. }, w) => {
            get_used(syn);
            get_used(w);
        }

        Apply(a, arr) =>
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
pub fn opt_remove_unused(knf: Knf) -> Knf {
    match knf {
        Let((a, t), val, w) => {
            if (used(a).not() && side_effect_free(val)) {
                opt_remove_unused(w);
            } else {
                Let((a, t), opt_remove_unused(val), opt_remove_unused(w));
            }
        }
        LetTuple(x, arr, w) =>
            LetTuple(x, arr, opt_remove_unused(w))
        LetRec({ name: name, ty: ty, args: args, body: syn }, w) =>
            LetRec({ name: name, ty: ty, args: args, body: opt_remove_unused(syn) }, opt_remove_unused(w))
        IfLe(a, b, body, otherwise) =>
            IfLe(a, b, opt_remove_unused(body), opt_remove_unused(otherwise))
        IfEq(a, b, body, otherwise) =>
            IfEq(a, b, opt_remove_unused(body), opt_remove_unused(otherwise))
        t => t
    }
}

pub fn opt(knf: Knf) -> Knf {
    get_used(knf);
    prepare_fundef(knf);

    opt_remove_unused(knf);
}