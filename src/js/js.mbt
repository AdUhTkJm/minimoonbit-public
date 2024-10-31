
fn emit_fn(fun: @closure.FuncDef) -> String {
    return "";
}

fn emit(program: @closure.Program) -> String {
    let _ = program.fundefs.map(emit_fn);
    return "";
}