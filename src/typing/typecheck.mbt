fn real(ty: @types.Type) -> @types.Type {
    match ty {
        Var(z) => {
            match z.val {
                Some(x) =>  {
                    let t = real(x);
                    z.val = Some(t);
                    t;
                }
                None => ty
            }
        }
        t => t
    }
}

fn unify(t1: @types.Type, t2: @types.Type) -> Unit {
    if (real(t1) == real(t2)) {
        return;
    }
    
    match (t1, t2) {
        (Var(x), Var(y)) => {
            if (x.val == None && y.val == None) {
                ();
            }
            if (x.val != None && y.val != None && real(x.val.unwrap()).weak_equal(real(y.val.unwrap())).not()) {
                @util.die("Type mismatch between \{x.val.unwrap()} (inferred) and \{y.val.unwrap()} (real)");
            }
            if (x.val == None && y.val != None) {
                x.val = y.val;
            }
            if (y.val == None && x.val != None) {
                y.val = x.val;
            }
        }
        (Var(x), y) | (y, Var(x)) => {
            if (x.val != None && real(t1).weak_equal(real(y)).not()) {
                @util.die("Type mismatch between \{x.val.unwrap()} (inferred) and \{y} (real)");
            }
            if (x.val == None) {
                x.val = Some(y);
            } else {
                unify(x.val.unwrap(), y);
            }
        }
        (Fun(a, b), Fun(c, d)) => {
            if (a.length() != c.length()) {
                @util.die("Type mismatch between \{a} and \{c}");
            }
            ignore(a.mapi(fn (i, z) { unify(z, c[i]) }));
            unify(b, d);
        }
        (Array(a), Array(b)) => {
            unify(a, b);
        }
        (Tuple(a), Tuple(b)) => {
            if (a.length() != b.length()) {
                @util.die("Type mismatch between \{a} and \{b}");
            }
            ignore(a.mapi(fn (i, z) { unify(z, b[i]) }));
        }
        _ => @util.die("Type mismatch: \{t1} and \{t2}");
    }
}

let eglob: Map[String, @types.Type] = Map::new();

pub let typing: Map[@types.Syntax, @types.Type] = Map::new();

pub fn lookup(ast: @types.Syntax) -> @types.Type {
    return real(typing[ast].unwrap());
}

pub fn infer(ast: @types.Syntax, env: @immut/hashmap.T[String, @types.Type], ~global: Bool = false) -> @types.Type {
    let z: @types.Type = match ast {
        Int(_) => Int
        Double(_) => Double
        Bool(_) => Bool
        Unit => Unit
        Tuple(arr) => Tuple(arr.map(fn (z) { infer(z, env) }))
        Array(_, elem) => Array(infer(elem, env))
        Get(x, inner) => {
            let arr_ty = infer(x, env);
            unify(infer(inner, env), Int);
            match real(arr_ty) {
                Array(z) => z
                _ => @util.die("Type mismatch: expected array, but got \{arr_ty}")
            }
        }
        Put(x, inner, assign) => {
            let arr_ty = infer(x, env);
            unify(infer(inner, env), Int);
            unify(arr_ty, Array(infer(assign, env)));
            Unit
        }
        Neg(a, ~kind = _) as n => {
            let t = infer(a, env);
            match t {
                Double => {
                    n.kind = Some(Double);
                    Double
                }
                _ => {
                    n.kind = Some(Int);
                    unify(t, Int);
                    Int
                }
            }
        }        
        Not(a) => {
            unify(infer(a, env), Bool);
            Bool
        }
        Var(x) => {
            match env[x] {
                Some(t) => t
                None => match eglob[x] {
                    Some(t) => t
                    None => Var(Ref::new(None)) 
                }
            }
        }
        LetRec({ name: (f_name, ty), args: args, body: syn }, w) => {
            if (global) {
                eglob[f_name] = ty;
            }
            let mut env_new = env.add(f_name, ty);
            for z in args {
                env_new = env_new.add(z.0, z.1);
            }
            unify(ty, Fun(args.map(fn (z) { z.1; }), infer(syn, env_new)));
            infer(w, env_new, ~global = global);
        }
        Let((name, ty), s1, s2) => {
            if (global) {
                eglob[name] = ty;
            }
            let env_new = env.add(name, ty);
            unify(ty, infer(s1, env_new));
            infer(s2, env_new, ~global = global);
        }
        LetTuple(arr, s1, s2) => {
            unify(Tuple(arr.map(fn (z) { z.1 })), infer(s1, env));
            let mut env_new = env;
            for z in arr {
                env_new = env_new.add(z.0, z.1);
            }
            infer(s2, env_new);
        }
        Prim(l, r, _, ~kind = _) as q => {
            let tl = infer(l, env);
            let tr = infer(r, env);
            unify(tl, tr);
            match (tl, tr) {
                (Var({ val: None } as z1), Var({ val: None } as z2)) => {
                    z1.val = Some(Int);
                    z2.val = Some(Int);
                }
                _ => ()
            }
            q.kind = if (real(tl) == Int) { Some(Int) } else { Some(Double) };
            tl;
        }
        App(f, args) => {
            let ret_ty: @types.Type = Var(Ref::new(None));
            let f_ty = infer(f, env);
            let args_ty = [];
            for z in args {
                args_ty.push(infer(z, env));
            }
            unify(f_ty, Fun(args_ty, ret_ty));
            ret_ty
        }
        If(cond, body, otherwise) => {
            unify(infer(cond, env), Bool);
            let ty = infer(body, env);
            unify(ty, infer(otherwise, env));
            ty
        }
        Eq(a, b) | LE(a, b) => {
            let ta = infer(a, env);
            let tb = infer(b, env);
            unify(ta, tb);
            Bool
        }
        ApplyExtern(_, args) => {
            // necessary for lookup()
            for z in args {
                ignore(infer(z, env));
            }
            Var(Ref::new(None))
        }
    }
    typing[ast] = z;
    z;
}

fn resolve(ty: @types.Type) -> @types.Type {
    match ty {
        Var({ val: Some(t) }) => t
        Var({ val: None }) => Unit
        Fun(arr, ty) => Fun(arr.map(resolve), resolve(ty))
        Tuple(arr) => Tuple(arr.map(resolve))
        Array(ty) => Array(resolve(ty))
        z => z
    }
}

pub fn typed(ast: @types.Syntax) -> @types.Syntax {
    match ast {
        LetRec({ name: (f_name, ty), args: args, body: syn }, w) =>
            LetRec({ name: (f_name, resolve(ty)), args: args.map(fn (z) { (z.0, resolve(z.1)) }), body: typed(syn) }, typed(w))
        Let((name, ty), s1, s2) =>
            Let((name, resolve(ty)), typed(s1), typed(s2))
        LetTuple(arr, s1, s2) =>
            LetTuple(arr.map(fn (z) { (z.0, resolve(z.1)) }), s1, s2)
        v => v
    }

}

pub fn typecheck(ast: @types.Syntax) -> @types.Syntax {
    eglob["print_char"] = Fun([Int], Unit);
    eglob["read_int"] = Fun([], Int);
    eglob["read_char"] = Fun([], Int);
    eglob["floor"] = Fun([Double], Double);
    eglob["abs_float"] = Fun([Double], Double);
    eglob["sqrt"] = Fun([Double], Double);
    eglob["sin"] = Fun([Double], Double);
    eglob["cos"] = Fun([Double], Double);
    eglob["atan"] = Fun([Double], Double);

    unify(infer(ast, @immut/hashmap.T::new(), ~global = true), Unit);
    return typed(ast);
}