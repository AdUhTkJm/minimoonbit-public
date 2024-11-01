struct ClosureInterpreter {
    extern_fns : Map[String, (Array[Value]) -> Value]
    functions : Array[@closure.FuncDef]
    mut env: @immut/hashmap.T[Name, Value]
}

pub typealias Name = @types.Name

pub typealias InterpreterLocalVars = @immut/hashmap.T[Name, Value]

pub enum Value {
    Unit
    Int(Int)
    Double(Double)
    Tuple(Array[Value])
    Array(Array[Value])
    ExternFn(String)
    Func(@closure.FuncDef, Array[Value])
} derive(Show)

pub fn Value::op_equal(self : Value, other : Value) -> Bool {
    match (self, other) {
        (Unit, Unit) => true
        (Int(x), Int(y)) => x == y
        (Double(x), Double(y)) => x == y
        (Tuple(xs), Tuple(ys)) => xs == ys
        (Array(xs), Array(ys)) => xs == ys
        (ExternFn(x), ExternFn(y)) => x == y
        (Func(_), Func(_)) => false
        _ => false
    }
}

pub fn ClosureInterpreter::new() -> ClosureInterpreter {
    { extern_fns: Map::new(), functions: [], env: @immut/hashmap.T::new() }
}

pub fn ClosureInterpreter::add_extern_fn(
    self : ClosureInterpreter,
    name : String,
    f : (Array[Value]) -> Value
) -> Unit {
    self.extern_fns.set(name, f)
}

fn find(self: ClosureInterpreter, name : Name) -> Value!Failure {
    for z in self.functions {
        if (z.old_name == name) {
            let env: Array[Value] = [];
            for i = 0; i < z.captured.length(); i = i + 1 {
                let x = z.captured[i]
                env.push(self.find!(x))
            }
            return Func(z, env);
        }
    }
    self.env.find(name).or_error!(Failure("variable not found: \{name} in env \{self.env}"))
}

pub fn ClosureInterpreter::eval_full(
    self : ClosureInterpreter,
    expr : @closure.Program
) -> Value!Failure {
    for f in expr.fundefs {
        self.functions.push(f);
    }
    self.eval!(expr.body)
}

pub fn ClosureInterpreter::eval(
    self : ClosureInterpreter,
    expr : @closure.Expr
) -> Value!Failure {
    match expr {
        Unit => Unit
        Int(i) => Int(i)
        Double(d) => Double(d)
        Var(v) | FVar(v) => self.find!(v)
        Neg(x) => {
            let x = self.find!(x)
            match x {
                Int(x) => Int(-x)
                _ => fail!("type mismatch, neg expects Int")
            }
        }
        Add(x, y) => {
            let x = self.find!(x)
            let y = self.find!(y)
            match (x, y) {
                (Int(x), Int(y)) => Int(x + y)
                _ => fail!("type mismatch, add expects Int")
            }
        }
        Sub(x, y) => {
            let x = self.find!(x)
            let y = self.find!(y)
            match (x, y) {
                (Int(x), Int(y)) => Int(x - y)
                _ => fail!("type mismatch, sub expects Int")
            }
        }
        Mul(x, y) => {
            let x = self.find!(x)
            let y = self.find!(y)
            match (x, y) {
                (Int(x), Int(y)) => Int(x * y)
                _ => fail!("type mismatch, mul expects Int")
            }
        }
        Div(x, y) => {
            let x = self.find!(x)
            let y = self.find!(y)
            match (x, y) {
                (Int(x), Int(y)) => Int(x / y)
                _ => fail!("type mismatch, div expects Int")
            }
        }
        FNeg(x) => {
            let x = self.find!(x)
            match x {
                Double(x) => Double(-x)
                _ => fail!("type mismatch, fneg expects Double")
            }
        }
        FAdd(x, y) => {
            let x = self.find!(x)
            let y = self.find!(y)
            match (x, y) {
                (Double(x), Double(y)) => Double(x + y)
                _ => fail!("type mismatch, fadd expects Double")
            }
        }
        FSub(x, y) => {
            let x = self.find!(x)
            let y = self.find!(y)
            match (x, y) {
                (Double(x), Double(y)) => Double(x - y)
                _ => fail!("type mismatch, fsub expects Double")
            }
        }
        FMul(x, y) => {
            let x = self.find!(x)
            let y = self.find!(y)
            match (x, y) {
                (Double(x), Double(y)) => Double(x * y)
                _ => fail!("type mismatch, fmul expects Double")
            }
        }
        FDiv(x, y) => {
            let x = self.find!(x)
            let y = self.find!(y)
            match (x, y) {
                (Double(x), Double(y)) => Double(x / y)
                _ => fail!("type mismatch, fdiv expects Double")
            }
        }
        Eq(x, y) => {
            let x = self.find!(x)
            let y = self.find!(y)
            match (x, y) {
                (Int(x), Int(y)) => Int(if (x == y) {1} else {0})
                (Double(x), Double(y)) => Int(if (x == y) {1} else {0})
                _ => fail!("type mismatch, eq expects Int / Double")
            }
            }
            Le(x, y) => {
            let x = self.find!(x)
            let y = self.find!(y)
            match (x, y) {
                (Int(x), Int(y)) => Int(if (x <= y) {1} else {0})
                (Double(x), Double(y)) => Int(if (x <= y) {1} else {0})
                _ => fail!("type mismatch, le expects Int / Double")
            }
        }
        BNeg(x) => {
            let x = self.find!(x)
            match x {
                Int(0) => Int(1)
                Int(1) => Int(0)
                _ => fail!("type mismatch, bneg expects Int(0) or Int(1)")
            }
        }
        IfEq(x, y, e1, e2) => {
            let x = self.find!(x)
            let y = self.find!(y)
            match (x, y) {
                (Int(x), Int(y)) =>
                    if x == y {
                        self.eval!(e1)
                    } else {
                        self.eval!(e2)
                    }
                (Double(x), Double(y)) =>
                    if x == y {
                        self.eval!(e1)
                    } else {
                        self.eval!(e2)
                    }
                _ => fail!("type mismatch, ifeq expects Int or Double")
            }
        }
        IfLe(x, y, e1, e2) => {
            let x = self.find!(x)
            let y = self.find!(y)
            match (x, y) {
                (Int(x), Int(y)) =>
                    if x <= y {
                        self.eval!(e1)
                    } else {
                        self.eval!(e2)
                    }
                (Double(x), Double(y)) =>
                    if x <= y {
                        self.eval!(e1)
                    } else {
                        self.eval!(e2)
                    }
                _ => fail!("type mismatch, ifle expects Int or Double")
            }
        }
        Let((x, _), e1, e2) => {
            let v = self.eval!(e1)
            self.env = self.env.add(x, v)
            self.eval!(e2)
        }
        CallExternal(l, xs) => {
            let args = []
            for x in xs {
                args.push(self.find!(x))
            }
            let ext_fn = self.extern_fns.get(l._).or_error!(Failure("function \{l} is not external"));
            ext_fn(args)
        }
        Call(n, xs) => {
            let args = [];
            for x in xs {
                args.push(self.find!(x));
            }
            match self.find!(n) {
                Func(def, env) => self.eval_fn!(env, def, args);
                _ => @util.die("call invoked on non-function \{n}")
            }
        }
        MakeTuple(xs) => {
            let vs = []
            for x in xs {
                vs.push(self.find!(x))
            }
            Tuple(vs)
        }
        LetTuple(xts, y, e) => {
            let mut new_env = self.env
            let y = self.find!(y)
            match y {
                Tuple(vs) => {
                    let len = xts.length()
                    if len != vs.length() {
                        fail!("tuple size mismatch")
                    }
                    for i = 0; i < len; i = i + 1 {
                        let (x, _) = xts[i]
                        new_env = new_env.add(x, vs[i])
                    }
                }
                _ => fail!("type mismatch, lettuple expects Tuple")
            }
            self.env = new_env;
            self.eval!(e)
        }
        ArrayGet(arr, idx) => {
            let arr = self.find!(arr)
            let idx = self.find!(idx)
            match (arr, idx) {
                (Array(arr), Int(idx)) => arr[idx]
                _ => fail!("type mismatch, get expects Array and Int")
            }
        }
        ArrayPut(arr, idx, v) => {
            let arr = self.find!(arr)
            let idx = self.find!(idx)
            let v = self.find!(v)
            match (arr, idx) {
                (Array(arr), Int(idx)) => arr[idx] = v
                _ => fail!("type mismatch, put expects Array and Int")
            }
            Unit
        }
        ExternalArray(_) => fail!("ExternalArray is not supported")
    }
}

pub fn ClosureInterpreter::eval_fn(self: ClosureInterpreter, copied: Array[Value], func: @closure.FuncDef, args: Array[Value]) -> Value!Failure {
    let mut env = self.env;
    for i = 0; i < func.args.length(); i = i + 1 {
        let (x, _) = func.args[i]
        env = env.add(x, args[i])
    }
    for i = 0; i < func.captured.length(); i = i + 1 {
        let x = func.captured[i]
        env = env.add(x, copied[i])
    }
    self.env = env.add(func.old_name, Func(func, copied));
    self.eval!(func.body)
}
