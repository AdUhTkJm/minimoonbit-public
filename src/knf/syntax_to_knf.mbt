pub typealias LocalEnv = @immut/hashmap.T[String, Type]

struct KnfEnv {
    mut counter : Int
    mut externals : @immut/hashmap.T[String, Type]
    mut names: @immut/hashmap.T[String, Name]
}

pub fn KnfEnv::new(externals : @immut/hashmap.T[String, Type]) -> KnfEnv {
    { counter: 1, externals, names: @immut/hashmap.T::new() }
}

pub let typing: Map[@types.Name, @types.Type] = Map::new();

pub fn KnfEnv::init_counter_from_existing(
    self : KnfEnv,
    existing : Knf
) -> Unit {
    self.counter = knf_max_counter(existing) + 1
}

fn KnfEnv::new_temp(self : KnfEnv) -> Name {
    let temp = Name::slot_only(self.counter)
    self.counter += 1
    temp
}

fn KnfEnv::new_named_temp(self : KnfEnv, name : Name) -> Name {
    let counter = self.counter
    self.counter += 1
    { ..name, slot: counter }
}

fn KnfEnv::get(self: KnfEnv, name: String) -> Name {
    return match self.names[name] {
        None => self.new_named_temp(Name::name_only(name));
        Some(t) => t
    }
}

fn KnfEnv::add(self: KnfEnv, name: String, ty: @types.Type) -> Unit {
    self.names = self.names.add(name, self.get(name));
    self.externals = self.externals.add(name, ty);
    typing[self.get(name)] = ty;
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
            Let((tx, Bool), self.to_knf(x), BNeg(tx))
        }
        Neg(x, ~kind = c) => {
            let tx = self.new_temp();
            match c {
                None | Some(Int) => Let((tx, Int), self.to_knf(x), Neg(tx))
                Some(Double) => Let((tx, Double), self.to_knf(x), FNeg(tx))
            }
        }
        Tuple(x) => {
            let t_args = x.map(fn (z) { ignore(z); self.new_temp() });

            x.foldi(~init = Tuple(t_args),
            fn (i, knf, arg) { Let((t_args[i], @typing.lookup(arg)), self.to_knf(arg), knf)});
        }
        Array(len, elem) => {
            let ety = @typing.lookup(elem);
            let ty = match ety {
                Int | Bool => "array"
                Double => "float_array"
                _ => "ptr_array"
            };
            let tl = self.new_temp();
            let te = self.new_temp();
            Let((tl, Int), self.to_knf(len),
            Let((te, ety), self.to_knf(elem),
            ExternalFunctionApplication("minimbt_create_\{ty}", [tl, te])));
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

                _ => @util.die("Internal error: to_knf()")
            }
            let ty = @typing.lookup(s);
            Let((a1, ty), self.to_knf(l), Let((a2, ty), self.to_knf(r), i));
        }
        Let((name, ty), s1, s2) => {
            self.add(name, ty);

            Let((self.get(name), ty), self.to_knf(s1), self.to_knf(s2));
        }
        LetRec({ name: (f_name, ty), args: args, body: syn }, w) => {
            self.add(f_name, ty);
            for z in args {
                self.add(z.0, z.1);
            }

            LetRec(FuncDef::{ name: self.get(f_name), ty: ty, args: args.map(fn (z) { (self.get(z.0), z.1) }), body: self.to_knf(syn)}, self.to_knf(w));
        }
        LetTuple(arr, syn, w) => {
            let x = arr.map(fn (z) { (self.new_temp(), z.1) });
            let cont = self.to_knf(w);
            let var = self.new_temp();
            Let((var, @typing.lookup(syn)), self.to_knf(syn), LetTuple(x, var, cont));
        }
        App(f, args) => {
            let t_args = args.map(fn (z) { ignore(z); self.new_temp() });
            let t_f = self.new_temp();
            Let((t_f, @typing.lookup(f)), self.to_knf(f),
                args.foldi(~init = Apply(t_f, t_args),
                fn (i, knf, arg) { Let((t_args[i], @typing.lookup(arg)), self.to_knf(arg), knf)}));
        }
        If(cond, body, otherwise) => {
            match cond {
                Eq(a, b) => {
                    let ta = self.new_temp();
                    let tb = self.new_temp();
                    Let((ta, @typing.lookup(a)), self.to_knf(a),
                    Let((tb, @typing.lookup(b)), self.to_knf(b),
                    IfEq(ta, tb, self.to_knf(body), self.to_knf(otherwise))))
                }
                LE(a, b) => {
                    let ta = self.new_temp();
                    let tb = self.new_temp();
                    Let((ta, @typing.lookup(a)), self.to_knf(a),
                    Let((tb, @typing.lookup(b)), self.to_knf(b),
                    IfLe(ta, tb, self.to_knf(body), self.to_knf(otherwise))))
                }
                _ => {
                    let ta = self.new_temp();
                    let tb = self.new_temp();
                    Let((ta, @typing.lookup(cond)), self.to_knf(cond),
                    Let((tb, Bool), Int(1),
                    IfEq(ta, tb, self.to_knf(body), self.to_knf(otherwise))))
                }
            }
        }
        Put(x, inner, assign) => {
            let tl = self.new_temp();
            let ti = self.new_temp();
            let ta = self.new_temp();
            Let((tl, @typing.lookup(x)), self.to_knf(x),
            Let((ti, @typing.lookup(inner)), self.to_knf(inner),
            Let((ta, @typing.lookup(assign)), self.to_knf(assign),
            Put(tl, ti, ta))))
        }
        Get(x, inner) => {
            let ta = self.new_temp();
            let tb = self.new_temp();
            Let((ta, @typing.lookup(x)), self.to_knf(x),
            Let((tb, @typing.lookup(inner)), self.to_knf(inner),
            Get(ta, tb)))
        }
        Eq(a, b) => {
            let ta = self.new_temp();
            let tb = self.new_temp();
            Let((ta, @typing.lookup(a)), self.to_knf(a),
            Let((tb, @typing.lookup(b)), self.to_knf(b),
            Eq(ta, tb)))
        }
        LE(a, b) => {
            let ta = self.new_temp();
            let tb = self.new_temp();
            Let((ta, @typing.lookup(a)), self.to_knf(a),
            Let((tb, @typing.lookup(b)), self.to_knf(b),
            Le(ta, tb)))
        }
    }
}
