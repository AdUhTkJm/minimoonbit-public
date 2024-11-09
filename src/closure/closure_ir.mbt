pub type Label String derive(Show, Eq, Hash)

pub typealias Name = @types.Name

pub typealias Type = @types.Type

pub enum Expr {
    Unit
    Int(Int)
    Double(Double)
    Neg(Name)
    Add(Name, Name)
    Sub(Name, Name)
    Mul(Name, Name)
    Div(Name, Name)
    FNeg(Name)
    BNeg(Name)
    FAdd(Name, Name)
    FSub(Name, Name)
    FMul(Name, Name)
    FDiv(Name, Name)
    Eq(Name, Name)
    Le(Name, Name)
    IfEq(Name, Name, Expr, Expr)
    IfLe(Name, Name, Expr, Expr)
    Let(Name, Expr, Expr)
    Var(Name)
    Call(Name, Array[Name])
    CallTailRec(Name, Array[Name])
    CallExternal(Label, Array[Name])
    MakeTuple(Array[Name])
    LetTuple(Array[Name], Name, Expr)
    ArrayGet(Name, Name)
    ArrayPut(Name, Name, Name)
    PackClosure(Name)
    CallClosure(Name, Array[Name])
    Deref(Name)
    Save(Name, Name)
    LShift(Name, Int)
} derive(Show, Eq)

pub fn Expr::hash(self: Expr) -> Int {
    return Hash::hash(self.to_string());
}

pub fn Expr::hash_combine(self: Expr, hasher: Hasher) -> Unit {
    return Hash::hash_combine(self.to_string(), hasher);
}

pub struct Closure {
    name : Label
    actual_free_vars : Array[Name]
} derive(Show)

pub struct FuncDef {
    name : Label
    old_name : Name
    mut is_closure : Bool
    mut args : Array[Name]
    mut captured : Array[Name]
    mut body : Expr
} derive(Show)

pub struct Program {
    mut fundefs : Array[FuncDef]
    mut body : Expr
} derive(Show)
