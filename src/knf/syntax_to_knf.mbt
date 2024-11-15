pub typealias LocalEnv = @immut/hashmap.T[String, Type]

struct KnfEnv {
    // Current counter for temporaries
    mut counter : Ref[Int]

    // The correspondence from identifier to Name
    mut names: @immut/hashmap.T[String, Name]

    // All global functions and variables
    mut globals: NameSet

    // Typing info in current scope
    mut env: @immut/hashmap.T[String, @types.Type]
}

pub let typing: Map[Name, Type] = Map::new();

pub fn KnfEnv::new(externals : @immut/hashmap.T[String, Type]) -> KnfEnv {
    ignore(externals);
    KnfEnv :: {
        counter: Ref::new(1),
        names: @immut/hashmap.T::new(),
        env: @immut/hashmap.T::new(),
        globals: NameSet::new(),
    };
}

pub fn KnfEnv::init_counter_from_existing(
    self : KnfEnv,
    existing : Knf
) -> Unit {
    self.counter.val = knf_max_counter(existing) + 1
}

fn KnfEnv::new_temp(self: KnfEnv, ty: Type) -> Name {
    let temp = Name::slot_only(self.counter.val);
    typing[temp] = ty;
    self.counter.val += 1;
    temp
}

fn KnfEnv::new_named_temp(self: KnfEnv, name: Name, ty: Type) -> Name {
    let counter = self.counter;
    let temp = { ..name, slot: counter.val };
    typing[temp] = ty;
    self.counter.val += 1;
    temp
}

fn KnfEnv::get(self: KnfEnv, name: String) -> Name {
    let x = self.names[name];
    if (x.is_empty()) {
        if (name == "main") {
            // Special case where main() might not be present
            self.add("main", Fun([], Unit));
            return self.get("main");
        }
        @util.die("knf: getting non-existent \{name}")
    }
    return x.unwrap();
}

fn KnfEnv::add(self: KnfEnv, name: String, ty: Type) -> Unit {
    self.env = self.env.add(name, ty);
    self.names = self.names.add(name, self.new_named_temp(Name::name_only(name), ty));
}

fn KnfEnv::lookup(self: KnfEnv, syn: @types.Syntax) -> @types.Type {
    return @typing.infer(syn, self.env);
}

fn KnfEnv::is_global(self: KnfEnv, name: String) -> Bool {
    for x in self.globals {
        if (x.0 == name) {
            return true;
        }
    }
    return false;
}

typealias NameSet = @immut/hashset.T[(String, Type)];

fn global_syntaxs(e: @types.Syntax) -> NameSet {
    match e {
        Let(a, _, c) => union_names(NameSet::from_array([a]), global_syntaxs(c))
        LetRec({ name: f_name, .. }, w) => union_names(NameSet::from_array([f_name]), global_syntaxs(w))
        _ => NameSet::new();
    }
}


pub fn KnfEnv::to_knf(self: KnfEnv, s: @types.Syntax) -> Knf {
    match s {
        Unit => Unit
        Int(x) => Int(x)
        Bool(true) => Int(1)
        Bool(false) => Int(0)
        Double(x) => Double(x)
        Var(x) => Var(self.get(x))
        Enum(_, _, w) => {
            // All info is stored in typing; no need to process this
            self.to_knf(w)
        }
        Not(x) => {
            let tx = self.new_temp(Int);
            Let(tx, self.to_knf(x), BNeg(tx))
        }
        Neg(x, ~kind = c) => {
            match c {
                None | Some(Int) => {
                    let tx = self.new_temp(Int);
                    Let(tx, self.to_knf(x), Neg(tx))
                }
                Some(Double) => {
                    let tx = self.new_temp(Double);
                    Let(tx, self.to_knf(x), FNeg(tx))
                }
            }
        }
        Tuple(x) => {
            let t_args = x.map(fn (z) { self.new_temp(self.lookup(z)) });

            x.foldi(~init = Tuple(t_args),
            fn (i, knf, arg) { Let(t_args[i], self.to_knf(arg), knf)});
        }
        Array(len, elem) => {
            let tl = self.new_temp(Int);
            let te = self.new_temp(self.lookup(elem));
            let array = match self.lookup(elem) {
                Double => "_float"
                Int => ""
                _ => "_ptr"
            }
            Let(tl, self.to_knf(len),
            Let(te, self.to_knf(elem),
            ExternalFunctionApplication("minimbt_create\{array}_array", [tl, te])));
        }
        Prim(l, r, op, ~kind = c) => {
            let ty: @types.Type = match c {
                None | Some(Int) => Int
                Some(Double) => Double
            };
            let a1 = self.new_temp(ty);
            let a2 = self.new_temp(ty);
            
            let i = match (op, c) {
                (Add, Some(Int)) => Add(a1, a2)
                (Sub, Some(Int)) => Sub(a1, a2)
                (Mul, Some(Int)) => Mul(a1, a2)
                (Div, Some(Int)) => Div(a1, a2)
                
                (Add, Some(Double)) => FAdd(a1, a2)
                (Sub, Some(Double)) => FSub(a1, a2)
                (Mul, Some(Double)) => FMul(a1, a2)
                (Div, Some(Double)) => FDiv(a1, a2)

                _ => @util.die("Illegal Prim: \{s}")
            }
            Let(a1, self.to_knf(l), Let(a2, self.to_knf(r), i));
        }
        Let((name, _), val, w) => {
            let env_new = { ..self };
            if (self.is_global(name).not()) {
                env_new.add(name, self.lookup(val));
            }

            Let(env_new.get(name), self.to_knf(val), env_new.to_knf(w));
        }
        LetRec({ name: (name, ty), args: args, body: syn }, w) => {
            let mut is_init = false;
            let f_name = 
                if (self.is_global(name) && name == "init") {
                    let new_name = "init_\{self.counter.val}";

                    is_init = true;
                    self.globals = self.globals.add((new_name, Fun([], Unit)));
                    new_name
                } else { name };

            if (self.is_global(f_name).not() || is_init) {
                self.add(f_name, ty);
            }


            // New scope started, deep copy current environment
            let env = KnfEnv :: { ..self };
            for z in args {
                env.add(z.0, z.1);
            }
            let e_args = args.map(fn (z) { env.get(z.0) });

            let fdef = FuncDef :: {
                name: self.get(f_name),
                ty: ty,
                args: e_args,
                body: env.to_knf(syn)
            };

            // Insert a fake global variable to call init()
            if (is_init) {
                let dummy = self.new_temp(Unit);
                LetRec(fdef, Let(dummy,
                Apply(self.get(f_name), []), self.to_knf(w)));
            } else {
                LetRec(fdef,
                self.to_knf(w));
            }
        }
        LetTuple(arr, syn, w) => {
            let var = self.new_temp(self.lookup(syn));
            for z in arr {
                if (self.is_global(z.0).not()) {
                    self.add(z.0, z.1);
                }
            }
            Let(var, self.to_knf(syn),
            LetTuple(arr.map(fn (z) { self.get(z.0) }), var, self.to_knf(w)))
        }
        App(f, args) => {
            let t_args = args.map(fn (z) { self.new_temp(self.lookup(z)) });
            let t_f = self.new_temp(self.lookup(f));
            Let(t_f, self.to_knf(f),
                args.foldi(~init = Apply(t_f, t_args),
                fn (i, knf, arg) { Let(t_args[i], self.to_knf(arg), knf)}));
        }
        Match(matcher, branches) => {
            let ty = self.lookup(matcher);
            let m = self.new_temp(ty);
            let en = @typing.get_enum(ty);
            let knf_b = [];
            for x in branches {
                let i = en.search_by(fn (z) { z.name == x.lead }).unwrap();
                let entry = en[i];
                let env_new =  { ..self };
                let _ = entry.binders.mapi(fn (i, z) {
                    env_new.add(x.binders[i], z);
                });

                let b = Branch :: {
                    lead: i,
                    binders: x.binders.map(fn (z) { env_new.get(z) }),
                    exec: env_new.to_knf(x.exec),
                };
                knf_b.push(b);
            }
            Let(m, self.to_knf(matcher),
            Match(m, knf_b));
        }
        If(cond, body, otherwise) => {
            match cond {
                Eq(a, b) => {
                    let ty = self.lookup(a);
                    let ta = self.new_temp(ty);
                    let tb = self.new_temp(ty);
                    Let(ta, self.to_knf(a),
                    Let(tb, self.to_knf(b),
                    IfEq(ta, tb, self.to_knf(body), self.to_knf(otherwise))))
                }
                Le(a, b) => {
                    let ty = self.lookup(a);
                    let ta = self.new_temp(ty);
                    let tb = self.new_temp(ty);
                    Let(ta, self.to_knf(a),
                    Let(tb, self.to_knf(b),
                    IfLe(ta, tb, self.to_knf(body), self.to_knf(otherwise))))
                }
                _ => {
                    let ta = self.new_temp(Int);
                    let tb = self.new_temp(Int);
                    Let(ta, self.to_knf(cond),
                    Let(tb, Int(1),
                    IfEq(ta, tb, self.to_knf(body), self.to_knf(otherwise))))
                }
            }
        }
        Put(x, inner, assign) => {
            let tl = self.new_temp(self.lookup(x));
            let ti = self.new_temp(self.lookup(inner));
            let ta = self.new_temp(self.lookup(assign));
            Let(tl, self.to_knf(x),
            Let(ti, self.to_knf(inner),
            Let(ta, self.to_knf(assign),
            Put(tl, ti, ta))))
        }
        Get(x, inner) => {
            let ta = self.new_temp(self.lookup(x));
            let tb = self.new_temp(self.lookup(inner));
            Let(ta, self.to_knf(x),
            Let(tb, self.to_knf(inner),
            Get(ta, tb)))
        }
        Eq(a, b) => {
            let ta = self.new_temp(self.lookup(a));
            let tb = self.new_temp(self.lookup(b));
            Let(ta, self.to_knf(a),
            Let(tb, self.to_knf(b),
            Eq(ta, tb)))
        }
        Le(a, b) => {
            let ta = self.new_temp(self.lookup(a));
            let tb = self.new_temp(self.lookup(b));
            Let(ta, self.to_knf(a),
            Let(tb, self.to_knf(b),
            Le(ta, tb)))
        }
        ApplyExtern(name, args) => {
            let t_args = args.map(fn (z) { self.new_temp(self.lookup(z)) });
            args.foldi(~init = ExternalFunctionApplication(name, t_args),
            fn (i, knf, arg) { Let(t_args[i], self.to_knf(arg), knf)});
        }
    }
}

pub fn KnfEnv::convert(self: KnfEnv, s: @types.Syntax) -> Knf {
    // We can always refer to a global variable before it is defined
    // So get global vars here
    self.globals = global_syntaxs(s);
    for x in self.globals {
        self.add(x.0, x.1);
    }

    // Add the constructors in enum
    // Note we have to supply all these constructors in RISC-V stage
    for k, v in @typing.e.enums {
        for x in v {
            self.add(x.name, Fun(x.binders, Enum(k)));
        };
    }
    
    self.to_knf(s);
}