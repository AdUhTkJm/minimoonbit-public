pub enum Syntax {
    Unit
    Bool(Bool)                                          // true false
    Int(Int)                                            // int
    Double(Double)                                      // double
    Var(String)                                         // _
    Tuple(Array[Syntax])                                // (_, _, _)
    Not(Syntax)                                         // not(_)
    Array(Syntax, Syntax)                               // Array::make(_, _)
    Neg(Syntax, mut ~kind : Kind?)                      // -_
    App(Syntax, Array[Syntax])                          // _(_, _, _) or _()
    Get(Syntax, Syntax)                                 // _[_]
    If(Syntax, Syntax, Syntax)                          // if _ { _ } else { _ }
    Prim(Syntax, Syntax, Op, mut ~kind : Kind?)         // _+ - * / _
    Eq(Syntax, Syntax)                                  // _==_
    Le(Syntax, Syntax)                                  // _<=_
    Let((String, Type), Syntax, Syntax)                 // let _: _ = _; _
    LetRec(Fundef, Syntax)                              // fn f() {} ; _
    LetTuple(Array[(String, Type)], Syntax, Syntax)     // let (_ , _) : (_, _)= _; _
    Put(Syntax, Syntax, Syntax)                         // _[_] = _
    ApplyExtern(String, Array[Syntax])                  // extern_function(_, _, ...)
    Match(Syntax, Array[Branch])                        // match _ { _ => _, ... }
    Enum(String, Array[EnumEntry], Syntax)              // enum _ { _ ... }; _
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

pub struct Branch {
    mut lead: String
    mut binders: Array[String]
    mut exec: Syntax
} derive(Show, Eq);

pub struct EnumEntry {
    mut name: String
    mut binders: Array[Type]
} derive(Show, Eq);

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
    Fun(Array[Type], Type)
    Tuple(Array[Type])
    Array(Type)
    Var(Ref[Option[Type]])
    Ptr
    Type(String)            // For unknown user-defined type
    Enum(String)            // For enum only
} derive(Show)

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
        (Type(x), Type(y)) => x == y
        (Enum(x), Enum(y)) => x == y
        _ => false
    }
}

pub fn Type::hash(self: Type) -> Int {
    return Hash::hash(self.to_string());
}

pub fn Type::hash_combine(self: Type, hasher: Hasher) -> Unit {
    return Hash::hash_combine(self.to_string(), hasher);
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
        (Type(x), Type(y)) => x == y
        (Enum(x), Enum(y)) => x == y
        _ => false
    }
}