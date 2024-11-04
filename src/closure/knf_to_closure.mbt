pub typealias LocalEnv = @immut/hashmap.T[Name, LowType]
typealias Set = @immut/hashset.T[@knf.Name]

// All global variables and functions
pub let glob: Ref[Set] = Ref::new(Set::new());
// Global variables only
pub let globvar: Ref[Set] = Ref::new(Set::new());


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
        LetTuple(arr, _, w) => union(Set::from_array(arr), globals(w))
        _ => Set::new();
    }
}

fn global_vars(e: @knf.Knf) -> Set {
    match e {
        Let(a, _, c) => union(Set::from_array([a]), global_vars(c))
        LetRec(_, w) => global_vars(w)
        LetTuple(arr, _, w) => union(Set::from_array(arr), global_vars(w))
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

        Neg(a) | BNeg(a) | FNeg(a) | Var(a) => 
            Set::from_array([a])

        ExternalFunctionApplication(_, args) => Set::from_array(args)
        Apply(f, args) | CallTailRec(f, args) => Set::from_array([f, ..args])
        Tuple(arr) => Set::from_array(arr)

        IfEq(a, b, l, r) | IfLe(a, b, l, r) => {
            let mut z = union(captured(l), captured(r));
            z = z.add(a).add(b);
            z
        }


        Let(x, val, w) => {
            union(captured(val), captured(w)).remove(x)
        }
        LetRec({ name: f_name, ty: _, args: args, body: syn }, w) => {
            let mut z = union(captured(w), captured(syn));
            for y in args {
                z = z.remove(y);
            }
            z.remove(f_name);
        }
        LetTuple(arr, n, w) => {
            let mut z = captured(w).add(n);
            for y in arr {
                z = z.remove(y);
            }
            z;
        }
    }
}

let funcs: Array[FuncDef] = [];

pub fn convert(knf: @knf.Knf) -> Expr {
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
            // Deal with multiple "init"s: combine them to one
            if (f_name.name == Some("init")) {
                for i = 0; i < funcs.length(); i = i + 1 {
                    let x = funcs[i];
                    if (x.old_name.name == Some("init")) {
                        let init = Name::name_only("__init_\{f_name}");
                        @knf.typing[init] = Fun([], Unit);
                        funcs[i] = {
                            ..x,
                            body: Let(init, x.body, convert(syn))
                        };
                        return convert(w);
                    }
                }
            }

            let mut caps = captured(syn).remove(f_name);
            for x in args {
                caps = caps.remove(x);
            }
            for x in glob.val {
                caps = caps.remove(x);
            }
            let cap = Array::from_iter(caps.iter());
            funcs.push(FuncDef :: {
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

pub fn closure(prog: @knf.Knf) -> Program {
    glob.val = globals(prog);
    globvar.val = global_vars(prog);
    let body = convert(prog);
    println(body);
    return Program::{ fundefs: funcs, body: body };
}
