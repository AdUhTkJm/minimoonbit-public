pub typealias LocalEnv = @immut/hashmap.T[String, Type]

struct KnfEnv {
    mut counter : Ref[Int]
    mut names: @immut/hashmap.T[String, Name]
}

pub fn KnfEnv::new(externals : @immut/hashmap.T[String, Type]) -> KnfEnv {
    ignore(externals);
    KnfEnv :: {
        counter: Ref::new(1),
        names: @immut/hashmap.T::new(),
    };
}

pub fn KnfEnv::init_counter_from_existing(
    self : KnfEnv,
    existing : Knf
) -> Unit {
    self.counter.val = knf_max_counter(existing) + 1
}

fn KnfEnv::new_temp(self : KnfEnv) -> Name {
    let temp = Name::slot_only(self.counter.val)
    self.counter.val += 1
    temp
}

fn KnfEnv::new_named_temp(self : KnfEnv, name : Name) -> Name {
    let counter = self.counter
    self.counter.val += 1
    { ..name, slot: counter.val }
}

fn KnfEnv::get(self: KnfEnv, name: String) -> Name {
    let x = self.names[name];
    if (x.is_empty()) {
        let w = self.new_named_temp(Name::name_only(name));
        self.names = self.names.add(name, w);
        return w;
    }
    return x.unwrap();
}

fn KnfEnv::add(self: KnfEnv, name: String) -> Unit {
    self.names = self.names.add(name, self.new_named_temp(Name::name_only(name)));
}

pub fn KnfEnv::to_knf(self: KnfEnv, s: @types.Syntax) -> Knf {
    match s {
        Unit => Unit
        Int(x) => Int(x)
        Bool(true) => Int(1)
        Bool(false) => Int(0)
        Double(x) => Double(x)
        Var(x) => Var(self.get(x))
        Not(x) => {
            let tx = self.new_temp();
            Let(tx, self.to_knf(x), BNeg(tx))
        }
        Neg(x, ~kind = c) => {
            let tx = self.new_temp();
            match c {
                None | Some(Int) => Let(tx, self.to_knf(x), Neg(tx))
                Some(Double) => Let(tx, self.to_knf(x), FNeg(tx))
            }
        }
        Tuple(x) => {
            let t_args = x.map(fn (z) { ignore(z); self.new_temp() });

            x.foldi(~init = Tuple(t_args),
            fn (i, knf, arg) { Let(t_args[i], self.to_knf(arg), knf)});
        }
        Array(len, elem) => {
            let tl = self.new_temp();
            let te = self.new_temp();
            Let(tl, self.to_knf(len),
            Let(te, self.to_knf(elem),
            ExternalFunctionApplication("minimbt_create_ptr_array", [tl, te])));
        }
        Prim(l, r, op, ~kind = c) => {
            let a1 = self.new_temp();
            let a2 = self.new_temp();
            
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
        Let((name, _), s1, s2) => {
            self.add(name);

            Let(self.get(name), self.to_knf(s1), self.to_knf(s2));
        }
        LetRec({ name: (f_name, ty), args: args, body: syn }, w) => {
            self.add(f_name);

            // New scope started, deep copy current environment
            let env = KnfEnv :: {
                counter: self.counter,
                names: self.names
            };
            for z in args {
                env.add(z.0);
            }
            let e_args = args.map(fn (z) { env.get(z.0) });

            LetRec(FuncDef::{ name: self.get(f_name), ty: ty, args: e_args, body: env.to_knf(syn)}, self.to_knf(w));
        }
        LetTuple(arr, syn, w) => {
            let var = self.new_temp();
            for z in arr {
                self.add(z.0);
            }
            Let(var, self.to_knf(syn),
            LetTuple(arr.map(fn (z) { self.get(z.0) }), var, self.to_knf(w)))
        }
        App(f, args) => {
            let t_args = args.map(fn (z) { ignore(z); self.new_temp() });
            let t_f = self.new_temp();
            Let(t_f, self.to_knf(f),
                args.foldi(~init = Apply(t_f, t_args),
                fn (i, knf, arg) { Let(t_args[i], self.to_knf(arg), knf)}));
        }
        If(cond, body, otherwise) => {
            match cond {
                Eq(a, b) => {
                    let ta = self.new_temp();
                    let tb = self.new_temp();
                    Let(ta, self.to_knf(a),
                    Let(tb, self.to_knf(b),
                    IfEq(ta, tb, self.to_knf(body), self.to_knf(otherwise))))
                }
                Le(a, b) => {
                    let ta = self.new_temp();
                    let tb = self.new_temp();
                    Let(ta, self.to_knf(a),
                    Let(tb, self.to_knf(b),
                    IfLe(ta, tb, self.to_knf(body), self.to_knf(otherwise))))
                }
                _ => {
                    let ta = self.new_temp();
                    let tb = self.new_temp();
                    Let(ta, self.to_knf(cond),
                    Let(tb, Int(1),
                    IfEq(ta, tb, self.to_knf(body), self.to_knf(otherwise))))
                }
            }
        }
        Put(x, inner, assign) => {
            let tl = self.new_temp();
            let ti = self.new_temp();
            let ta = self.new_temp();
            Let(tl, self.to_knf(x),
            Let(ti, self.to_knf(inner),
            Let(ta, self.to_knf(assign),
            Put(tl, ti, ta))))
        }
        Get(x, inner) => {
            let ta = self.new_temp();
            let tb = self.new_temp();
            Let(ta, self.to_knf(x),
            Let(tb, self.to_knf(inner),
            Get(ta, tb)))
        }
        Eq(a, b) => {
            let ta = self.new_temp();
            let tb = self.new_temp();
            Let(ta, self.to_knf(a),
            Let(tb, self.to_knf(b),
            Eq(ta, tb)))
        }
        Le(a, b) => {
            let ta = self.new_temp();
            let tb = self.new_temp();
            Let(ta, self.to_knf(a),
            Let(tb, self.to_knf(b),
            Le(ta, tb)))
        }
        ApplyExtern(name, args) => {
            let t_args = args.map(fn (z) { ignore(z); self.new_temp() });
            args.foldi(~init = ExternalFunctionApplication(name, t_args),
            fn (i, knf, arg) { Let(t_args[i], self.to_knf(arg), knf)});
        }
    }
}