pub fn Expr::to_json(self : Expr) -> Json {
    match self {
        Expr::Unit => ["Unit"]
        Expr::Int(i) => ["Int", Number(i.to_double())]
        Expr::Double(d) => ["Double", Number(d)]
        Expr::Neg(n) => ["Neg", n.to_json()]
        Expr::Add(n1, n2) => ["Add", n1.to_json(), n2.to_json()]
        Expr::Sub(n1, n2) => ["Sub", n1.to_json(), n2.to_json()]
        Expr::Mul(n1, n2) => ["Mul", n1.to_json(), n2.to_json()]
        Expr::Div(n1, n2) => ["Div", n1.to_json(), n2.to_json()]
        Expr::FNeg(n) => ["FNeg", n.to_json()]
        Expr::FAdd(n1, n2) => ["FAdd", n1.to_json(), n2.to_json()]
        Expr::FSub(n1, n2) => ["FSub", n1.to_json(), n2.to_json()]
        Expr::FMul(n1, n2) => ["FMul", n1.to_json(), n2.to_json()]
        Expr::FDiv(n1, n2) => ["FDiv", n1.to_json(), n2.to_json()]
        Expr::IfEq(n1, n2, e1, e2) =>
            ["IfEq", n1.to_json(), n2.to_json(), e1.to_json(), e2.to_json()]
        Expr::IfLe(n1, n2, e1, e2) =>
            ["IfLe", n1.to_json(), n2.to_json(), e1.to_json(), e2.to_json()]
        Expr::Let(n, e1, e2) =>
            ["Let", n.to_json(), e1.to_json(), e2.to_json()]
        Expr::Var(n) => ["Var", n.to_json()]
        Expr::Call(n, ns) => ["Call", n.to_json(), ns.to_json()]
        Expr::CallExternal(l, ns) => ["CallExternal", l._.to_json(), ns.to_json()]
        Expr::MakeTuple(ns) => ["MakeTuple", ns.to_json()]
        Expr::LetTuple(n_ts, n, e) => {
            let n_ts_res = []
            for it in n_ts {
                n_ts_res.push(it.to_json())
            }
            ["LetTuple", n_ts_res.to_json(), n.to_json(), e.to_json()]
        }
        Expr::ArrayGet(n1, n2) => ["ArrayGet", n1.to_json(), n2.to_json()]
        Expr::ArrayPut(n1, n2, n3) =>
            ["ArrayPut", n1.to_json(), n2.to_json(), n3.to_json()]
        _ => []
    }
}

pub fn Expr::from_json(json : Json) -> Expr! {
    match json {
        ["Unit"] => Expr::Unit
        ["Int", Number(i)] => Expr::Int(i.to_int())
        ["Double", Number(d)] => Expr::Double(d)
        ["Neg", n] => Expr::Neg(Name::from_json!(n))
        ["Add", n1, n2] => Expr::Add(Name::from_json!(n1), Name::from_json!(n2))
        ["Sub", n1, n2] => Expr::Sub(Name::from_json!(n1), Name::from_json!(n2))
        ["Mul", n1, n2] => Expr::Mul(Name::from_json!(n1), Name::from_json!(n2))
        ["Div", n1, n2] => Expr::Div(Name::from_json!(n1), Name::from_json!(n2))
        ["FNeg", n] => Expr::FNeg(Name::from_json!(n))
        ["FAdd", n1, n2] => Expr::FAdd(Name::from_json!(n1), Name::from_json!(n2))
        ["FSub", n1, n2] => Expr::FSub(Name::from_json!(n1), Name::from_json!(n2))
        ["FMul", n1, n2] => Expr::FMul(Name::from_json!(n1), Name::from_json!(n2))
        ["FDiv", n1, n2] => Expr::FDiv(Name::from_json!(n1), Name::from_json!(n2))
        ["IfEq", n1, n2, e1, e2] =>
            Expr::IfEq(
                Name::from_json!(n1),
                Name::from_json!(n2),
                Expr::from_json!(e1),
                Expr::from_json!(e2),
            )
        ["IfLe", n1, n2, e1, e2] =>
            Expr::IfLe(
                Name::from_json!(n1),
                Name::from_json!(n2),
                Expr::from_json!(e1),
                Expr::from_json!(e2),
            )
        ["Let", n, e1, e2] =>
            Expr::Let(
                (Name::from_json!(n)),
                Expr::from_json!(e1),
                Expr::from_json!(e2),
            )
        ["Var", n] => Expr::Var(Name::from_json!(n))
        ["Call", n, Array(ns)] => {
            let ns_res = []
            for n in ns {
                ns_res.push(Name::from_json!(n))
            }
            Expr::Call(Name::from_json!(n), ns_res)
        }
        ["CallExternal", String(l), Array(ns)] => {
            let ns_res = []
            for n in ns {
                ns_res.push(Name::from_json!(n))
            }
            Expr::CallExternal(Label(l), ns_res)
        }
        ["MakeTuple", Array(ns)] => {
            let ns_res = []
            for n in ns {
                ns_res.push(Name::from_json!(n))
            }
            Expr::MakeTuple(ns_res)
        }
        ["LetTuple", Array(n_ts), n, e] => {
            let n_ts_res = []
            for it in n_ts {
                match it {
                    n => n_ts_res.push(Name::from_json!(n))
                }
            }
            Expr::LetTuple(n_ts_res, Name::from_json!(n), Expr::from_json!(e))
        }
        ["ArrayGet", n1, n2] =>
            Expr::ArrayGet(Name::from_json!(n1), Name::from_json!(n2))
        ["ArrayPut", n1, n2, n3] =>
            Expr::ArrayPut(
                Name::from_json!(n1),
                Name::from_json!(n2),
                Name::from_json!(n3),
            )
        _ => fail!("invalid json")
    }
}

pub fn Closure::to_json(self : Closure) -> Json {
    {
        "name": self.name._.to_json(),
        "actual_free_vars": self.actual_free_vars.to_json(),
    }
}

pub fn Closure::from_json(json : Json) -> Closure! {
    match json {
        { "name": String(name), "actual_free_vars": Array(actual_free_vars) } => {
            let actual_free_vars_res = []
            for n in actual_free_vars {
                actual_free_vars_res.push(Name::from_json!(n))
            }
            { name: Label(name), actual_free_vars: actual_free_vars_res }
        }
        _ => fail!("invalid json")
    }
}

pub fn FuncDef::to_json(self : FuncDef) -> Json {
    {
        "name": self.name._.to_json(),
        "old_name": self.old_name.to_json(),
        "is_closure": self.is_closure.to_json(),
        "args": {
            let res = []
            for nt in self.args {
                res.push(Json::Array([nt.to_json()]))
            }
            Array(res)
        },
        "formal_free_vars": {
            let res = []
            for nt in self.captured {
                let n = nt
                res.push(Json::Array([n.to_json()]))
            }
            Array(res)
        },
        "body": self.body.to_json(),
    }
}

pub fn FuncDef::from_json(json : Json) -> FuncDef! {
    match json {
        {
            "name": String(name),
            "old_name": n,
            "is_closure": b,
            "args": Array(args),
            "formal_free_vars": Array(formal_free_vars),
            "body": body,
        } => {
            let args_res = []
            for nt in args {
                match nt {
                    n => args_res.push(Name::from_json!(n))
                }
            }
            let formal_free_vars_res = []
            for nt in formal_free_vars {
                match nt {
                    [n] =>
                        formal_free_vars_res.push(
                            (Name::from_json!(n)),
                        )
                    _ => fail!("invalid json")
                }
            }
            {
                name: Label(name),
                old_name: Name::from_json!(n),
                is_closure: @json.from_json!(b),
                args: args_res,
                captured: formal_free_vars_res,
                body: Expr::from_json!(body),
            }
        }
        _ => fail!("invalid json")
    }
}

pub fn Program::to_json(self : Program) -> Json {
    {
        "fundefs": Array(self.fundefs.map(FuncDef::to_json)),
        "body": self.body.to_json(),
    }
}

pub fn Program::from_json(json : Json) -> Program! {
    match json {
        { "fundefs": Array(fundefs), "body": body } => {
            let fundefs_res = []
            for f in fundefs {
                fundefs_res.push(FuncDef::from_json!(f))
            }
            { fundefs: fundefs_res, body: Expr::from_json!(body) }
        }
        _ => fail!("invalid json")
    }
}
