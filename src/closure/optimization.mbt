let transformed: Array[FuncDef] = [];

fn returnable(expr: Expr) -> @immut/hashset.T[Name] {
    match expr {
        IfLe(_, _, body, otherwise) | IfEq(_, _, body, otherwise) =>
            union(returnable(body), returnable(otherwise))
        Let(_, _, w) =>
            returnable(w)
        LetTuple(_, _, w) =>
            returnable(w)
        Var(x) =>
            @immut/hashset.T::from_array([x])
        _ =>
            @immut/hashset.T::new()
    }
}

fn opt_do_transform(expr: Expr) -> Expr {
    match expr {
        Call(f, args) => {
            let i = transformed.search_by(fn (x) { x.old_name == f });
            if (i.is_empty()) {
                expr
            } else {
                let fdef = transformed[i.unwrap()];
                amend(fdef.captured.fold(~init = Call(f, args + fdef.captured), fn (total, x) {
                    Let(x, Var(x), total); // Stub; incomplete
                }));
            }
        }
        IfLe(a, b, body, otherwise) =>
            IfLe(a, b, opt_do_transform(body), opt_do_transform(otherwise))
        IfEq(a, b, body, otherwise) =>
            IfEq(a, b, opt_do_transform(body), opt_do_transform(otherwise))
        Let(x, val, w) =>
            Let(x, val, opt_do_transform(w))
        LetTuple(arr, val, w) =>
            LetTuple(arr, val, opt_do_transform(w))
        t => t
    }
}

/// If a closure has never been released,
/// then transform it to non-closure
pub fn opt_transform_closure(program: Program) -> Program {
    let mut retfns: @immut/hashset.T[Name] = @immut/hashset.T::new();
    
    for x in program.fundefs {
        retfns = union(retfns, returnable(x.body));
    }

    for x in program.fundefs {
        if (x.is_closure && retfns.contains(x.old_name).not()) {
            transformed.push(x);
        }
    }

    let funcs: Array[FuncDef] = [];

    for x in program.fundefs {
        let cl = retfns.contains(x.old_name) || (x.args + x.captured).length() > 8;
        funcs.push(FuncDef :: {
            name: x.name,
            old_name: x.old_name,
            is_closure: cl,
            args: if (cl) { x.args } else { x.args + x.captured },
            captured: if (cl) { x.captured } else { [] },
            body: opt_do_transform(x.body)
        })
    }

    program.fundefs = funcs;
    return program;
}

pub struct OptEnv {
    // All names used in the program
    mut used_names: @immut/hashset.T[@types.Name]
}

let e: OptEnv = OptEnv :: {
    used_names: @immut/hashset.T::new(),
}

fn OptEnv::add_used(self: OptEnv, arr: Array[Name]) -> Unit {
    self.used_names = union(self.used_names, @immut/hashset.T::from_array(arr));
}

fn get_used(expr: Expr) -> Unit {
    match expr {
        Add(a, b) | Sub(a, b) | Mul(a, b) | Div(a, b) |
        FAdd(a, b) | FSub(a, b) | FMul(a, b) | FDiv(a, b) |
        Eq(a, b) | Le(a, b) | ArrayGet(a, b) =>
            e.add_used([a, b]);

        Neg(a) | BNeg(a) | FNeg(a) | Var(a) | PackClosure(a) =>
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
        ArrayPut(_) => false
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
    for x in program.fundefs {
        get_used(x.body);
        x.body = opt_remove_unused_(x.body);
    }
    return program;
}