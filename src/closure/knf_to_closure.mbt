pub typealias LocalEnv = @immut/hashmap.T[Name, LowType]
typealias Set = @immut/hashset.T[@knf.Name]

// All global variables and functions
pub let glob: Ref[Set] = Ref::new(Set::new());
// Global variables only
pub let globvar: Ref[Set] = Ref::new(Set::new());

pub struct ClosureEnv {
    mut prog: Program

    mut cnt: Int
}

pub let t: ClosureEnv = ClosureEnv :: {
    prog: Program :: { fundefs: [], body: Unit },
    cnt: 1000000
};

fn union(a: Set, b: Set) -> Set {
    let mut l = a;
    for z in b {
        l = l.add(z);
    }
    l;
}

fn globals(e: @knf.Knf) -> Set {
    match e {
        Let(a, _, c) => union(Set::from_array([a]), globals(c))
        LetRec({ name: f_name, .. }, w) => union(Set::from_array([f_name]), globals(w))
        _ => Set::new();
    }
}

fn global_vars(e: @knf.Knf) -> Set {
    match e {
        Let(a, _, c) => union(Set::from_array([a]), global_vars(c))
        LetRec(_, w) => global_vars(w)
        _ => Set::new();
    }
}

fn captured(e: @knf.Knf) -> Set {
    match e {
        Int(_) | Double(_) | Unit => Set::new()

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
            let ff = find_function(a);
            if (ff.is_empty()) {
                Set::from_array([a])
            } else {
                Set::from_array([a, ..ff.unwrap().captured]);
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


fn convert(knf: @knf.Knf) -> Expr {
    match knf {
        Unit => Unit
        Int(x) => Int(x)
        Double(x) => Double(x)
        Add(a, b) => Add(a, b)
        Sub(a, b) => Sub(a, b)
        Mul(a, b) => Mul(a, b)
        Div(a, b) => Div(a, b)
        FAdd(a, b) => FAdd(a, b)
        FSub(a, b) => FSub(a, b)
        FMul(a, b) => FMul(a, b)
        FDiv(a, b) => FDiv(a, b)
        Eq(a, b) => Eq(a, b)
        Le(a, b) => Le(a, b)
        Var(x) => Var(x)
        Neg(a) => Neg(a)
        FNeg(a) => FNeg(a)
        BNeg(a) => BNeg(a)
        Tuple(arr) => MakeTuple(arr)
        Put(x, inner, v) => ArrayPut(x, inner, v)
        Get(x, inner) => ArrayGet(x, inner)

        ExternalFunctionApplication(name, args) => CallExternal(name, args)

        Let(name, b, c) => Let(name, convert(b), convert(c))

        IfEq(a, b, c, d) => IfEq(a, b, convert(c), convert(d))
        IfLe(a, b, c, d) => IfLe(a, b, convert(c), convert(d))

        LetTuple(arr, val, w) => LetTuple(arr, val, convert(w))

        Apply(f, args) => Call(f, args)
        CallTailRec(f, args) => CallTailRec(f, args)
        
        LetRec({ name: f_name, ty: _, args: args, body: syn }, w) => {
            let mut caps = captured(syn).remove(f_name);
            for x in args {
                caps = caps.remove(x);
            }
            for x in glob.val {
                caps = caps.remove(x);
            }

            let cap = Array::from_iter(caps.iter());
            t.prog.fundefs.push(FuncDef :: {
                name: f_name.name.unwrap(),
                old_name: f_name,
                is_closure: cap.length() != 0,
                args: args,
                captured: cap,
                body: convert(syn),
            });
            convert(w)
        }
    }
}

/// If x is one of the functions
/// (not about whether x is of type Fun(...))
fn is_function(x: Name) -> Bool {
    return t.prog.fundefs.search_by(fn (f) { f.old_name == x }).is_empty().not();
}

fn find_function(x: Name) -> Option[FuncDef] {
    let i = t.prog.fundefs.search_by(fn (f) { f.old_name == x });
    match i {
        Some(j) => Some(t.prog.fundefs[j])
        None => None
    }
}


/// Annotates closure operation to facilitate RISC-V stage
fn amend(expr: Expr) -> Expr {
    match expr {
        Var(f) => {
            if (is_function(f)) {
                PackClosure(f);
            } else {
                Var(f)
            }
        }
        IfLe(a, b, body, otherwise) =>
            IfLe(a, b, amend(body), amend(otherwise))
        IfEq(a, b, body, otherwise) =>
            IfEq(a, b, amend(body), amend(otherwise))
        Let(x, val, w) =>
            Let(x, amend(val), amend(w));
        LetTuple(arr, val, w) =>
            LetTuple(arr, val, amend(w))
        Call(f, args) => {
            match @knf.value_of(f) {
                Fun(f_name) => {
                    if (find_function(f_name).unwrap().is_closure) {
                        CallClosure(f, args)
                    } else {
                        Call(f_name, args);
                    }
                }
                _ => CallClosure(f, args);
            }
        }
        CallTailRec(f, args) => {
            match @knf.value_of(f) {
                Fun(f_name) => CallTailRec(f_name, args)
                _ => @util.die("closure: tail-rec failed on \{f}")
            }
        }
        t => t
    }
}

fn initial(prog: @knf.Knf) -> Program {
    glob.val = globals(prog);
    globvar.val = global_vars(prog);
    let body = convert(prog);
    t.prog.body = body;

    return t.prog;
}

pub fn closure(prog: @knf.Knf) -> Program {
    t.prog = initial(prog);

    for x in t.prog.fundefs {
        // This is to tackle with the situation where
        // x returns a function;
        // in which case, without let, no PackClosure will be present
        x.body = amend(x.body);
    }

    t.prog.body = amend(t.prog.body);
    
    let opt = t.prog
        |> opt_remove_unused;

    return opt;
}