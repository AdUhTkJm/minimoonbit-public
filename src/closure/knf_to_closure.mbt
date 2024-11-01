pub typealias LocalEnv = @immut/hashmap.T[Name, LowType]
typealias Set = @immut/hashset.T[@knf.Name]

// All global variables and functions
pub let glob: Ref[Set] = Ref::new(Set::new());


fn union(a: Set, b: Set) -> Set {
    let mut l = a;
    for z in b {
        l = l.add(z);
    }
    l;
}

fn globals(e: @knf.Knf) -> Set {
    match e {
        Let((a, _), _, c) => union(Set::from_array([a]), globals(c))
        LetRec({ name: f_name, .. }, w) => union(Set::from_array([f_name]), globals(w))
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

        ExternalArray(_) => @util.die("External array not supported")
        ExternalFunctionApplication(_, args) => Set::from_array(args)
        Apply(f, args) => Set::from_array([f, ..args])
        Tuple(arr) => Set::from_array(arr)

        IfEq(a, b, l, r) | IfLe(a, b, l, r) => {
            let mut z = union(captured(l), captured(r));
            z = z.add(a).add(b);
            z
        }


        Let((x, _), val, w) => {
            union(captured(val), captured(w)).remove(x)
        }
        // LetRec is special; we don't want to process more,
        // since this is already a self-contained function
        LetRec({ name: f_name, ty: _, args: args, body: syn }, _) => {
            let mut z = captured(syn);
            for y in args {
                z = z.remove(y.0);
            }
            z.remove(f_name);
        }
        LetTuple(arr, n, w) => {
            let mut z = captured(w).add(n);
            for y in arr {
                z = z.remove(y.0);
            }
            z;
        }
    }
}

pub fn lowtype(x: @types.Type) -> LowType {
    match @typing.real(x) {
        Int => Int
        Double => Double
        Unit => Unit
        Bool => Int
        Tuple(x) => Tuple(x.map(lowtype))
        Array(x) => Array(lowtype(x))
        Ptr => Ptr
        Fun(args, ret) => Fun(args.map(lowtype), lowtype(ret))
        _ => @util.die("Can't appear here: \{x}");
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

        ExternalArray(_) => @util.die("External array is not supported")
        ExternalFunctionApplication(name, args) => CallExternal(name, args)

        Let((name, ty), b, c) => Let((name, lowtype(ty)), convert(b), convert(c))

        IfEq(a, b, c, d) => IfEq(a, b, convert(c), convert(d))
        IfLe(a, b, c, d) => IfLe(a, b, convert(c), convert(d))

        LetTuple(arr, val, w) => LetTuple(arr.map(fn (z) { (z.0, lowtype(z.1)) }), val, convert(w))

        Apply(f, args) => Call(f, args)
        
        LetRec({ name: f_name, ty: ty, args: args, body: syn }, w) => {
            let mut caps = captured(knf);
            for x in glob.val {
                caps = caps.remove(x);
            }
            let cap = Array::from_iter(caps.iter());
            let lowty = lowtype(ty);
            funcs.push(FuncDef :: {
                name: f_name.name.unwrap(),
                old_name: f_name,
                is_closure: cap.length() != 0,
                ty: lowty,
                args: args.map(fn (z) { (z.0, lowtype(z.1)) }),
                captured: cap.map(fn (z) { (z, lowtype(@knf.typing[z].unwrap())) }),
                body: convert(syn),
            });
            convert(w)
        }
        
    }
}

pub fn closure(prog: @knf.Knf) -> Program {
    glob.val = globals(prog);
    let body = convert(prog);
    return Program::{ fundefs: funcs, body: body };
}
