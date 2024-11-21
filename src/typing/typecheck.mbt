pub struct TypingEnv {
    // Lookup table from String to enums
    mut enums: Map[String, Array[@types.EnumEntry]];
}

pub fn TypingEnv::new() -> TypingEnv {
    return TypingEnv :: {
        enums: Map::new(),
    }
}

pub let e: TypingEnv = TypingEnv::new();

pub fn get_enum(ty: @types.Type) -> Array[@types.EnumEntry] {
    match real(ty) {
        Enum(s) => {
            if (e.enums.contains(s).not()) {
                @util.die("typing: \{ty} is not an enum")
            }
            e.enums[s].unwrap();
        }
        _ => @util.die("typing: \{ty} is not an enum")
    }
}

pub fn real(ty: @types.Type) -> @types.Type {
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
        Type(z) => {
            if (e.enums.contains(z)) {
                Enum(z);
            } else {
                @util.die("typing: cannot identify type \{z}");
            }
        }
        Fun(arr, ret) => Fun(arr.map(real), real(ret));
        Array(ty) => Array(real(ty));
        Tuple(arr) => Tuple(arr.map(real));
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
                @util.die("typing: type mismatch: \{x.val.unwrap()} (inferred); \{y.val.unwrap()} (real)");
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
                @util.die("typing: type mismatch: \{x.val.unwrap()} (inferred); \{y} (real)");
            }
            if (x.val == None) {
                x.val = Some(y);
            } else {
                unify(x.val.unwrap(), y);
            }
        }
        (Fun(a, b), Fun(c, d)) => {
            if (a.length() != c.length()) {
                @util.die("typing: type mismatch: \{a}; \{c}");
            }
            ignore(a.mapi(fn (i, z) { unify(z, c[i]) }));
            unify(b, d);
        }
        (Array(a), Array(b)) => {
            unify(a, b);
        }
        (Tuple(a), Tuple(b)) => {
            if (a.length() != b.length()) {
                @util.die("typing: type mismatch: \{a}; \{b}");
            }
            ignore(a.mapi(fn (i, z) { unify(z, b[i]) }));
        }
        _ => @util.die("typing: type mismatch: \{t1}; \{t2}");
    }
}

let eglob: Map[String, @types.Type] = Map::new();

let typing: Map[@types.Syntax, @types.Type] = Map::new();

pub fn lookup(syntax: @types.Syntax) -> @types.Type {
    match typing[syntax] {
        Some(x) => x
        None => @util.die("type: no known type of \{syntax}");
    }
}

pub fn infer(ast: @types.Syntax, env: @immut/hashmap.T[String, @types.Type], ~global: Bool = false) -> @types.Type {
    let result: @types.Type = match ast {
        Int(_) => Int
        Double(_) => Double
        Bool(_) => Bool
        Unit => Unit
        Tuple(arr) => Tuple(arr.map(fn (z) { infer(z, env) }))
        Array(len, elem) => {
            unify(infer(len, env), Int);
            Array(infer(elem, env))
        }
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
            match real(t) {
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
            let env_new = env.add(f_name, ty);
            let mut env_local = env_new;
            for z in args {
                env_local = env_local.add(z.0, z.1);
            }
            unify(ty, Fun(args.map(fn (z) { z.1; }), infer(syn, env_local)));
            infer(w, env_new, ~global = global);
        }
        Let((name, ty), val, w) => {
            if (global) {
                eglob[name] = ty;
            }
            let env_new = env.add(name, ty);
            unify(ty, infer(val, env_new));
            infer(w, env_new, ~global = global);
        }
        LetTuple(arr, val, w) => {
            unify(Tuple(arr.map(fn (z) { z.1 })), infer(val, env));
            let mut env_new = env;
            for z in arr {
                env_new = env_new.add(z.0, z.1);
            }
            infer(w, env_new);
        }
        Enum(name, entries, w) => {
            let mut env_new = env;

            // Each constructor is viewed as a function
            for z in entries {
                env_new = env_new.add(z.name, Fun(z.binders, Enum(name)))
            }

            e.enums[name] = entries;
            infer(w, env_new);
        }
        Match(matcher, branches) => {
            let ty = real(infer(matcher, env));
            let ret_ty: @types.Type = Var(Ref::new(None));

            match ty {
                Enum(s) => {
                    if (e.enums.contains(s).not()) {
                        @util.die("typing: no such enum: \{s}");
                    }
                    let en = e.enums[s].unwrap();
                    for x in branches {
                        let i = en.search_by(fn (z) { z.name == x.lead });
                        if (i.is_empty()) {
                            @util.die("typing: enum \{s} does not have constructor \{x.lead}");
                        }
                        let entry = en[i.unwrap()];
                        if (entry.binders.length() != x.binders.length()) {
                            @util.die("typing: incorrect binder for constructor \{x.lead}")
                        }
                        let mut env_new = env;
                        let _ = entry.binders.mapi(fn (i, z) {
                            let y = x.binders[i];
                            env_new = env_new.add(y, z);
                        });
                        unify(ret_ty, infer(x.exec, env_new));
                    }
                }
                _ => @util.die("typing: matching non-enum: \{ty}");
            }
            ret_ty;
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
        Eq(a, b) | Le(a, b) => {
            let ta = infer(a, env);
            let tb = infer(b, env);
            unify(ta, tb);
            Bool
        }
        ApplyExtern(_, args) => {
            let _ = args.map(fn (x) { infer(x, env) });
            Var(Ref::new(None))
        }
    };
    typing[ast] = result;
    result
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

fn add_name(names: @immut/hashmap.T[String, String], x: String) -> @immut/hashmap.T[String, String] {
    // We can have multiple "fn init {...}"; it is legal
    // We added { "main": "main" } at the beginning of deconflict(), so don't need to add one more
    return if (names.find(x).is_empty() || x == "init" || x == "main") {
        names.add(x, x);
    } else {
        names.add(x, "\{names[x].unwrap()}_");
    }
}

/// Rename variables so that there are no variables of the same name, in the same scope.
fn deconflict(ast: @types.Syntax, names: @immut/hashmap.T[String, String]) -> @types.Syntax {
    match ast {
        LetRec({ name: (f_name, ty), body: syn, args: args }, w) => {
            let env = add_name(names, f_name);
            let mut local = env;
            for x in args {
                local = add_name(local, x.0);
            }
            LetRec({
                name: (env[f_name].unwrap(), ty),
                body: deconflict(syn, local),
                args: args.map(fn (x) { (local[x.0].unwrap(), x.1) }),
            }, deconflict(w, env));
        }

        Let((a, t), val, w) => {
            let env = add_name(names, a);
            Let((env[a].unwrap(), t), deconflict(val, names), deconflict(w, env));
        }

        LetTuple(arr, x, w) => {
            let mut env = names;
            for x in arr {
                env = add_name(env, x.0);
            }
            LetTuple(arr.map(fn (x) { (env[x.0].unwrap(), x.1) }), deconflict(x, names), deconflict(w, env));
        }

        If(cond, body, otherwise) =>
            If(deconflict(cond, names), deconflict(body, names), deconflict(otherwise, names));

        Prim(a, b, op, ~kind = c) =>
            Prim(deconflict(a, names), deconflict(b, names), op, ~kind = c);

        Eq(a, b) =>
            Eq(deconflict(a, names), deconflict(b, names))

        Le(a, b) =>
            Le(deconflict(a, names), deconflict(b, names))

        Get(a, b) =>
            Get(deconflict(a, names), deconflict(b, names))

        Put(a, b, x) =>
            Put(deconflict(a, names), deconflict(b, names), deconflict(x, names))

        ApplyExtern(name, args) =>
            ApplyExtern(name, args.map(fn (x) { deconflict(x, names) }))

        App(f, args) =>
            App(deconflict(f, names), args.map(fn (x) { deconflict(x, names) }))
        
        Neg(a, ~kind = c) =>
            Neg(deconflict(a, names), ~kind = c);

        Not(a) =>
            Not(deconflict(a, names));

        Var(w) =>
            match names[w] {
                None => Var(w)      // This only happens for global variables
                                    // And any conflict will cause crash
                Some(x) => Var(x)
            }

        Tuple(arr) =>
            Tuple(arr.map(fn (x) { deconflict(x, names) }))

        Array(len, elem) =>
            Array(deconflict(len, names), deconflict(elem, names))

        t => t
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
    // It is possible that there are no main()
    // But we added the call to main() beforehand
    let d = deconflict(ast, @immut/hashmap.T::new().add("main", "main"));

    unify(infer(d, @immut/hashmap.T::new(), ~global = true), Unit);

    return typed(d);
}