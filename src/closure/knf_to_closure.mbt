pub typealias LocalEnv = @immut/hashmap.T[Name, LowType]
typealias Set = @immut/hashset.T[@knf.Name]

fn union(a: Set, b: Set) -> Set {
    let mut l = a;
    for z in b {
        l = a.add(z);
    }
    a;
}

let typing: Map[Name, LowType] = Map::new();

fn captured(e: @knf.Knf) -> Set {
    match e {
        Int(_) | Double(_) | Unit => @immut/hashset.T::new()

        Var(z) => {
            typing[z] = lowtype(@knf.typing[z].unwrap());
            @immut/hashset.T::from_array([z])
        }

        Add(a, b) | Sub(a, b) | Mul(a, b) | Div(a, b) => {
            typing[a] = Int;
            typing[b] = Int;
            @immut/hashset.T::from_array([a, b])
        }
        FAdd(a, b) | FSub(a, b) | FMul(a, b) | FDiv(a, b) => {
            typing[a] = Double;
            typing[b] = Double;
            @immut/hashset.T::from_array([a, b])
        }
        Eq(a, b) | Le(a, b) => {
            @immut/hashset.T::from_array([a, b])
        }


        Apply(f, args) => @immut/hashset.T::from_array([f, ..args])

        Let((x, t), val, w) => {
            typing[x] = lowtype(t);
            union(captured(val), captured(w)).remove(x)
        }
        LetRec({ name: f_name, ty: ty, args: args, body: syn }, w) => {
            let mut z = captured(syn).remove(f_name)
            for y in args {
                z = z.remove(y.0);
                typing[y.0] = lowtype(y.1);
            }
            union(z, captured(w)).remove(f_name);
        }
        LetTuple(arr, n, w) => {
            let mut z = captured(w);
            for y in arr {
                z = z.remove(y.0);
                typing[y.0] = lowtype(y.1);
            }
            z;
        }
        
        z => @util.die("Undefined \{z}")
    }
}

pub fn lowtype(x: @types.Type) -> LowType {
    match x {
        Int => Int
        Double => Double
        Unit => Unit
        Bool => Int
        Tuple(x) => Tuple(x.map(lowtype))
        Array(x) => Array(lowtype(x))
        Ptr => Ptr
        Fun(args, ret) => ClosureFn(args.map(lowtype), lowtype(ret))
        _ => @util.die("Can't appear here: \{x}");
    }
}

let funcs: Array[FuncDef] = [];
pub fn convert(knf: @knf.Knf, extern_env: Map[String, Type]) -> Expr {
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

        ExternalArray(_) => @util.die("External array is not supported")
        ExternalFunctionApplication(name, args) => CallDirect(name, args)

        Let((name, ty), b, c) => Let((name, lowtype(ty)), convert(b, extern_env), convert(c, extern_env))

        IfEq(a, b, c, d) => IfEq(a, b, convert(c, extern_env), convert(d, extern_env))
        IfLe(a, b, c, d) => IfLe(a, b, convert(c, extern_env), convert(d, extern_env))

        LetTuple(arr, val, w) => LetTuple(arr.map(fn (z) { (z.0, lowtype(z.1)) }), val, convert(w, extern_env))

        Apply(f, args) => {
            let mut val = CallClosure(f, args);
            for z in funcs {
                if (z.old_name == f) {
                    if (z.is_closure.not()) {
                        val = CallDirect(z.name, args)
                    }
                    break;
                }
            }
            val
        }
        LetRec({ name: f_name, ty: ty, args: args, body: syn }, w) => {
            let cap = Array::from_iter(captured(knf).iter());
            let lowty = lowtype(ty);
            println("\{f_name}(...) captured \{cap}");
            funcs.push(FuncDef :: {
                name: f_name.name.unwrap(),
                old_name: f_name,
                is_closure: true,
                ty: lowty,
                args: args.map(fn (z) { (z.0, lowtype(z.1)) }),
                formal_free_vars: cap.map(fn (z) { (z, typing[z].unwrap()) }),
                body: convert(syn, extern_env)
            });
            MakeClosure((f_name, lowty), Closure::{ name: f_name.name.unwrap(), actual_free_vars: cap }, convert(w, extern_env))
        }
        
    }
}

pub fn knf_program_to_closure(
    prog : @knf.Knf,
    extern_env : Map[String, Type]
) -> Program {
    let body = convert(prog, extern_env);
    return Program::{ fundefs: funcs, body: body };
}
