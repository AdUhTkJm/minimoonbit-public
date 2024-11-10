pub typealias Name = @types.Name

pub typealias Type = @types.Type

pub enum Knf {
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
    IfEq(Name, Name, Knf, Knf)
    IfLe(Name, Name, Knf, Knf)
    Let(Name, Knf, Knf)
    Var(Name)
    LetRec(FuncDef, Knf)
    Apply(Name, Array[Name])
    Tuple(Array[Name])
    LetTuple(Array[Name], Name, Knf)
    Get(Name, Name)
    Put(Name, Name, Name)
    ExternalFunctionApplication(String, Array[Name])
    CallTailRec(Name, Array[Name])
    ConstTuple(Array[Constant])
    ExternalArray(Array[Constant])
} derive(Show, Eq)

pub struct FuncDef {
    name : Name
    ty : Type
    args : Array[Name]
    mut body : Knf
} derive(Show, Eq)
