pub enum Syntax {
    Unit
    Bool(Bool) // true false
    Int(Int) // int
    Double(Double) // double
    Var(String) // _
    Tuple(Array[Syntax]) // (_, _, _)
    Not(Syntax) // not(_)
    Array(Syntax, Syntax) // Array::make(_, _)
    Neg(Syntax, mut ~kind : Kind?) // -_
    App(Syntax, Array[Syntax]) // _(_, _, _) or _()
    Get(Syntax, Syntax) // _[_]
    If(Syntax, Syntax, Syntax) // if _ { _ } else { _ }
    Prim(Syntax, Syntax, Op, mut ~kind : Kind?) // _+ - * / _
    Eq(Syntax, Syntax) // _==_
    Le(Syntax, Syntax) // _<=_
    Let((String, Type), Syntax, Syntax) // let _: _ = _; _
    LetRec(Fundef, Syntax) // fn f() {} ; _
    LetTuple(Array[(String, Type)], Syntax, Syntax) // let (_ , _) : (_, _)= _; _
    Put(Syntax, Syntax, Syntax) // _[_] = _
    ApplyExtern(String, Array[Syntax]) // extern_function(_, _, ...)
} derive(Show, Eq)

pub fn Syntax::hash(self: Syntax) -> Int {
        return Hash::hash(self.to_string());
}

pub fn Syntax::hash_combine(self: Syntax, hasher: Hasher) -> Unit {
        return Hash::hash_combine(self.to_string(), hasher);
}

pub enum Kind {
    Int
    Double
} derive(Show, Eq)

pub enum Op {
    Add
    Sub
    Mul
    Div
} derive(Show, Eq)

pub struct Fundef {
    name : (String, Type)
    args : Array[(String, Type)]
    body : Syntax
} derive(Show, Eq)

pub enum Type {
    Unit
    Bool
    Int
    Double
    Fun(Array[Type], Type) // (_, _, _) -> _
    Tuple(Array[Type]) // (_, _, _)
    Array(Type) // Array[_]
    Var(Ref[Type?])
    Ptr
} derive(Show)

pub fn Type::is_ptr_like(self : Type) -> Bool {
    match self {
        Fun(_) | Tuple(_) | Array(_) | Ptr => true
        Var(t) =>
            match t.val {
                Some(t) => t.is_ptr_like()
                None => false
            }
        _ => false
    }
}

pub fn Type::is_float_like(self : Type) -> Bool {
    match self {
        Double => true
        Var(t) =>
            match t.val {
                Some(t) => t.is_float_like()
                None => false
            }
        _ => false
    }
}

pub fn Type::size_of(self : Type, size_of_ptr : Int) -> Int {
    match self {
        Unit => 0
        Bool => 4
        Int => 4
        Double => 8
        Tuple(_) | Fun(_, _) | Array(_) | Ptr => size_of_ptr
        Var(t) =>
            match t.val {
                Some(t) => t.size_of(size_of_ptr)
                None => @util.die("Uninstantiated type variable")
            }
    }
}

pub fn Type::op_equal(self : Type, other : Type) -> Bool {
    match (self, other) {
        (Unit, Unit) => true
        (Bool, Bool) => true
        (Int, Int) => true
        (Double, Double) => true
        (Fun(xs, x), Fun(ys, y)) => xs == ys && x == y
        (Tuple(xs), Tuple(ys)) => xs == ys
        (Array(x), Array(y)) => x == y
        (Ptr, Ptr) => true
        (Var(x), Var(y)) => x.val == y.val
        _ => false
    }
}

pub fn Type::weak_equal(self : Type, other : Type) -> Bool {
    match (self, other) {
        (Unit, Unit) => true
        (Bool, Bool) => true
        (Int, Int) => true
        (Double, Double) => true
        (Fun(xs, x), Fun(ys, y)) => xs.foldi(~init = true, fn (i, r, z) { z.weak_equal(ys[i]) && r }) && x.weak_equal(y)
        (Tuple(xs), Tuple(ys)) => xs.foldi(~init = true, fn (i, r, z) { z.weak_equal(ys[i]) && r })
        (Array(x), Array(y)) => x.weak_equal(y)
        (Ptr, Ptr) => true
        (Var(x), Var(y)) => x.val == y.val || x.val == None || y.val == None
        (y, Var(x)) | (Var(x), y) => x.val == None || x.val.unwrap() == y
        _ => false
    }
}