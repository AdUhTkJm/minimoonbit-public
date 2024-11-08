// All external functions that runtime provides
pub let externs: Array[String] =
    ["print_int", "print_endline", "truncate", "print_char",
    "read_int", "read_char", "int_of_float", "float_of_int",
    "sin", "cos", "atan", "sqrt", "abs_float", "floor"];

let asm: Array[RvAsm] = [];

struct T {
    // For spilling registers
    mut offset: Int

    // The first instruction where a register is written to
    mut first_used: Map[@types.Name, Int]

    // The first instruction where a register is read from
    mut last_used: Map[@types.Name, Int]

    // The register for each name in IR
    mut regs: Map[@types.Name, Reg]
    
    // Which name occupies the register?
    mut occupy: Map[Reg, @types.Name]

    // Temporary register count (for intermediate results)
    mut rcnt: Int

    // Label count (for if-else, while etc.)
    mut labelcount: Int

    // All functions
    mut funcs: Array[@closure.FuncDef]
}

fn T::new() -> T {
    T :: {
        offset: 0,
        first_used: Map::new(),
        last_used: Map::new(),
        regs: Map::new(),
        occupy: Map::new(),
        rcnt: @closure.t.cnt + 1,
        labelcount: 0,
        funcs: [],
    }
}

fn t_clear() -> Unit {
    t.offset = 0;
    t.occupy = Map::new();
    t.first_used = Map::new();
    t.last_used = Map::new();
    t.regs = Map::new();
}


pub let t: T = T::new();


fn reg(r: @types.Name, has_call: Bool) -> Unit {
    let mut list = [];

    // If no calling other functions, prefer temp variables
    if (type_of(r) == Double) {
        if (has_call) {
            list = freg_allocatable_list;
        } else {
            list = freg_allocatable_list_biased;
        }
    } else {
        if (has_call) {
            list = reg_allocatable_list;
        } else {
            list = reg_allocatable_list_biased;
        }
    }

    for z in list {
        // z is used after this instruction, so can't reuse
        if (t.occupy.contains(z) && t.last_used[t.occupy[z].unwrap()] > t.first_used[r]) {
            continue;
        }

        t.occupy[z] = r;
        t.regs[r] = z;
        
        return;
    }
    
    // Spill
    if (type_of(r) == Double) {
        t.regs[r] = SpiltDouble(t.offset);
    } else {
        t.regs[r] = Spilt(t.offset);
    }
    t.offset += 8;
}

// Produce a fake register
fn fake(ty: @types.Type) -> Reg {
    let name = @types.Name::slot_only(t.rcnt);
    let z = Fake(name);
    @knf.typing[name] = ty;
    t.rcnt += 1;
    z
}

fn find_func(a: @types.Name) -> Option[@closure.FuncDef] {
    for f in t.funcs {
        if (f.old_name == a) {
            return Some(f);
        }
    }
    None
}


// Returns the @types.Name for a register, if it is a fake one
fn real(reg: Reg) -> @types.Name {
    match reg {
        Fake(name) => name
        _ => @util.die("non-fake")
    }
}

fn is_fake(reg: Reg) -> Bool {
    match reg {
        Fake(_) => true
        _ => false
    }
}

fn visited(reg: Reg) -> Bool {
    match reg {
        Fake(name) => t.first_used.contains(name)
        _ => false
    }
}

fn store_first(reg: Option[Reg], i: Int) -> Unit {
    match reg {
        Some(Fake(name)) => t.first_used[name] = i;
        _ => ()
    }
}

fn store_last(reg: Option[Reg], i: Int) -> Unit {
    match reg {
        Some(Fake(name)) => t.last_used[name] = i;
        _ => ()
    }
}

fn type_of(name: @types.Name) -> @types.Type {
    match @knf.typing[name] {
        Some(x) => @typing.real(x)
        _ => @util.die("emit: cannot determine type of \{name}")
    }
}

/// It just scans through.
/// to deal with loops, special taken must be taken in PREVIOUS stages.
/// Updates t.regs[] to store registers.
fn basic_regalloc(asm: Array[RvAsm]) -> Unit {
    let to_alloc: Array[@types.Name] = [];

    // Record all assigned registers
    // Find the first and last times where they are accessed
    for i = 0; i < asm.length(); i = i + 1 {
        let used = reg_used(asm[i]);
        if (used.rd.is_empty().not() && is_fake(used.rd.unwrap()) && visited(used.rd.unwrap()).not()) {
            store_first(used.rd, i);
            to_alloc.push(real(used.rd.unwrap()));
        }

        store_last(used.rd, i);
        store_last(used.rs1, i);
        store_last(used.rs2, i);
    }

    let mut has_call = false;
    for x in asm {
        match x {
            Call(_) | Jalr(_) => has_call = true;
            _ => ()
        }
    }

    to_alloc.sort_by(fn (a, b) { t.first_used[a].unwrap() - t.first_used[b].unwrap(); });

    for r in to_alloc {
        if (@closure.glob.val.contains(r)) {
            continue;
        }
        reg(r, has_call);
    }
}

/// Eliminates the main call that gets added in parser
/// We will call main later on, in emit_main
pub fn eliminate_main_call(expr: @closure.Expr) -> @closure.Expr {
    match expr {
        Let(a, val, w) => {
            // The final command of body will be a call to main()
            // So instead of making it a closure (in tidy())
            // we will directly compile it into a call
            match val {
                PackClosure({ name: Some("main"), .. }) |
                Var({ name: Some("main"), .. })=> Unit
                    
                _ => Let(a, val, eliminate_main_call(w))
            }
        }
        Call(x, _) => if (x.name == Some("main")) { Unit } else { expr }
        _ => @util.die("emit: unexpected global: \{expr}");
    }
}

// Return value: where the result of this expression is stored
fn emit_expr(expr: @closure.Expr) -> Reg {
    match expr {
        Unit => fake(Unit)
        Var(x) => Fake(x)
        Int(x) => {
            let r = fake(Int);
            asm.push(Li(r, x.to_string()));
            r;
        }
        Double(x) => {
            let tmp = fake(Int);
            let r = fake(Double);
            asm.push(Li(tmp, x.reinterpret_as_i64().to_string()));
            asm.push(FmvDX(r, tmp));
            r;
        }
        Add(a, b) => {
            let r = fake(Int);
            asm.push(Add(r, Fake(a), Fake(b)));
            r;
        }
        Sub(a, b) => {
            let r = fake(Int);
            asm.push(Sub(r, Fake(a), Fake(b)));
            r;
        }
        Div(a, b) => {
            let r = fake(Int);
            asm.push(Div(r, Fake(a), Fake(b)));
            r;
        }
        Mul(a, b) => {
            let r = fake(Int);
            asm.push(Mul(r, Fake(a), Fake(b)));
            r;
        }
        FAdd(a, b) => {
            let r = fake(Double);
            asm.push(FaddD(r, Fake(a), Fake(b)));
            r;
        }
        FSub(a, b) => {
            let r = fake(Double);
            asm.push(FsubD(r, Fake(a), Fake(b)));
            r;
        }
        FDiv(a, b) => {
            let r = fake(Double);
            asm.push(FdivD(r, Fake(a), Fake(b)));
            r;
        }
        FMul(a, b) => {
            let r = fake(Double);
            asm.push(FmulD(r, Fake(a), Fake(b)));
            r;
        }
        FNeg(a) => {
            let r = fake(Double);
            asm.push(FnegD(r, Fake(a)));
            r;
        }
        Eq(a, b) => {
            let r = fake(Int);
            if (type_of(a) == Double) {
                asm.push(FeqD(r, Fake(a), Fake(b)));
            } else {
                asm.push(Xor(r, Fake(a), Fake(b)));
                asm.push(Sltiu(r, r, 1));
            }
            r;
        }
        Le(a, b) => {
            let r = fake(Int);
            if (type_of(a) == Double) {
                asm.push(FleD(r, Fake(a), Fake(b)));
            } else {
                asm.push(Slt(r, Fake(b), Fake(a)));
                asm.push(Xori(r, r, 1));
            }
            r;
        }
        Neg(a) => {
            let r = fake(Int);
            asm.push(Sub(r, Zero, Fake(a)));
            r;
        }
        BNeg(a) => {
            let r = Fake(a);
            asm.push(Xori(r, r, 1));
            r;
        }
        ArrayGet(x, i) => {
            let ty = match type_of(x) {
                Array(w) => w
                _ => @util.die("emit: array get in non-array (\{x}: \{type_of(x)})");
            }
            let r = fake(Ptr);
            // r = *(x + (i << 3));
            asm.push(Slli(r, Fake(i), 3));
            asm.push(Add(r, r, Fake(x)));

            let result = fake(ty);

            if (ty == Double) {
                asm.push(Fld(result, { base: r, offset: 0 }));
            } else {
                asm.push(Ld(result, { base: r, offset: 0 }));
            }
            result
        }
        ArrayPut(x, i, val) => {
            let addr = fake(Int);
            // *(x + (i << 3)) = val;
            asm.push(Slli(addr, Fake(i), 3));
            asm.push(Add(addr, addr, Fake(x)));

            if (type_of(val) == Double) {
                asm.push(Fsd(Fake(val), { base: addr, offset: 0 }));
            } else {
                asm.push(Sd(Fake(val), { base: addr, offset: 0 }));
            }
            fake(Unit);
        }
        MakeTuple(arr) => {
            let r = fake(Tuple(arr.map(type_of)));

            // Allocate an array for the tuple
            asm.push(Li(A0, (8 * arr.length()).to_string()));
            asm.push(Call("minimbt_create_ptr_array"));

            // Put everything into the array
            let _ = arr.mapi(fn (i, x) {
                if (type_of(x) == Double) {
                    asm.push(Fsd(Fake(x), { base: A0, offset: i * 8 }));
                } else {
                    asm.push(Sd(Fake(x), { base: A0, offset: i * 8 }));
                }
            });

            // Record the array address
            asm.push(Mv(r, A0));
            r;
        }
        IfEq(a, b, body, otherwise) => {
            let l_else = "else_\{t.labelcount}";
            let end = "end_\{t.labelcount}";
            t.labelcount += 1;
            
            let ty: @types.Type = match type_of(a) {
                Int => Int
                Double => Double
                _ => @util.die("emit: type error in if-eq (\{a}: \{type_of(a)})");
            };

            if (ty == Int) {
                asm.push(Bne(Fake(a), Fake(b), l_else));
            } else {
                let tmp = fake(Int);
                asm.push(FeqD(tmp, Fake(a), Fake(b)));
                asm.push(Beq(tmp, Zero, l_else));
            }
            
            let e_body = emit_expr(body);
            let r = fake(type_of(real(e_body)));

            asm.push(Mv(r, e_body));
            asm.push(J(end));
            asm.push(Label(l_else));

            asm.push(Mv(r, emit_expr(otherwise)));
            asm.push(Label(end));
            
            r;
        }
        IfLe(a, b, body, otherwise) => {
            let l_else = "else_\{t.labelcount}";
            let end = "end_\{t.labelcount}";
            t.labelcount += 1;

            let ty: @types.Type = match type_of(a) {
                Int => Int
                Double => Double
                _ => @util.die("emit: type error in if-eq (\{a}: \{type_of(a)})");
            };

            if (ty == Int) {
                asm.push(Bgt(Fake(a), Fake(b), l_else));
            } else {
                let tmp = fake(Int);
                asm.push(FleD(tmp, Fake(a), Fake(b)));
                asm.push(Beq(tmp, Zero, l_else));
            }
            
            let e_body = emit_expr(body);
            let r = fake(type_of(real(e_body)));

            asm.push(Mv(r, e_body));
            asm.push(J(end));
            asm.push(Label(l_else));

            asm.push(Mv(r, emit_expr(otherwise)));
            asm.push(Label(end));
            r;
        }
        Let(a, val, w) => {
            let rv = emit_expr(val);

            asm.push(Mv(Fake(a), rv));
            emit_expr(w);
        }
        LetTuple(arr, val, w) => {
            let _ = arr.mapi(fn (i, x) {
                if (type_of(x) == Double) {
                    asm.push(Fld(Fake(x), { base: Fake(val), offset: i * 8 }));
                } else {
                    asm.push(Ld(Fake(x), { base: Fake(val), offset: i * 8 }));
                }
            });
            emit_expr(w);
        }
        CallExternal(name, args) => {
            // The only external we used is create_**_array
            if (args.length() > 1) {
                match type_of(args[1]) {
                    Double => asm.push(FmvD(Fa0, Fake(args[1])));
                    _ => asm.push(Mv(A1, Fake(args[1])));
                }

                asm.push(Mv(A0, Fake(args[0])));
                asm.push(Call(name._));
                
                let rv = fake(Array(type_of(args[1])));
                asm.push(Mv(rv, A0));
                rv
            } else {
                // We don't care; the other ones are for print_int etc.
                // and they will be removed anyway
                fake(Unit);
            }
        }
        Call(name, args) => {
            // Guaranteed that name is directly callable

            let _ = args.mapi(fn (i, x) {
                match type_of(x) {
                    Double(_) => asm.push(FmvD(Farg(i), Fake(x)));
                    _ => asm.push(Mv(Arg(i), Fake(x)));
                }
            });

            asm.push(Call(name_fn(name)));

            let ret_ty = match type_of(name) {
                Fun(_, r) => r
                _ => @util.die("emit: calling non-function: \{type_of(name)}")
            }
            let rv = fake(ret_ty);
            asm.push(Mv(rv, match ret_ty {
                Double => Fa0
                _ => A0
            }));
            rv
        }
        CallTailRec(name, args) => {
            // Guaranteed that name is directly callable

            let f = find_func(name).unwrap();

            let _ = args.mapi(fn (i, x) {
                asm.push(Mv(Fake(f.args[i]), Fake(x)));
            });

            let _ = f.captured.map(fn (x) {
                match type_of(x) {
                    Double => asm.push(FmvD(Fake(x), Fake(x)));
                    _ => asm.push(Mv(Fake(x), Fake(x)));
                };
            });

            asm.push(J("\{f.old_name}_tailrec"));

            let ret_ty = match type_of(name) {
                Fun(_, r) => r
                _ => @util.die("emit: calling non-function: \{type_of(name)}")
            }
            let rv = fake(ret_ty);
            asm.push(Mv(rv, match ret_ty {
                Double => Fa0
                _ => A0
            }));
            rv
        }
        PackClosure(f) => {
            fn pack(f) {
                let r = fake(Ptr);
                let ff = find_func(f).unwrap();
                let result = fake(type_of(f));

                let amap = {};

                for x in ff.captured {
                    if (find_func(x).is_empty()) {
                        amap[x] = Fake(x);
                    } else {
                        amap[x] = pack(x);
                    }
                }

                asm.push(La(r, name_fn(f)));
                asm.push(Li(A0, (8 + ff.captured.length() * 8).to_string()));
                asm.push(Call("minimbt_malloc"));
                asm.push(Sd(r, { base: A0, offset: 0 }));
                let _ = ff.captured.mapi(fn (i, x) {
                    match type_of(x) {
                        Double => asm.push(Fsd(amap[x].unwrap(), { base: A0, offset: 8 + i * 8 }));
                        _ => asm.push(Sd(amap[x].unwrap(), { base: A0, offset: 8 + i * 8 }));
                    }
                });

                asm.push(Mv(result, A0));
                return result;
            }
            pack(f)
        }
        CallClosure(closure, args) => {
            let f = fake(Ptr);

            asm.push(Ld(f, { base: Fake(closure), offset: 0 }));
            asm.push(Mv(Arg(args.length()), Fake(closure)));

            let _ = args.mapi(fn (i, x) {
                match type_of(x) {
                    Double(_) => asm.push(FmvD(Farg(i), Fake(x)));
                    _ => asm.push(Mv(Arg(i), Fake(x)));
                }
            });

            asm.push(Jalr(f));

            let ret_ty = match type_of(closure) {
                Fun(_, r) => r
                _ => @util.die("emit: calling non-function: \{type_of(closure)}")
            }
            let rv = fake(ret_ty);
            asm.push(Mv(rv, match ret_ty {
                Double => Fa0
                _ => A0
            }));
            rv
        }
    }
}

// Returns the name of a function
fn name_fn(f_name: @types.Name) -> String {
    if (externs.contains(f_name.name.unwrap())) {
        "minimbt_" + f_name.name.unwrap()
    } else {
        f_name.to_string()
    }
}


// If referencing global things, make it correct
fn tidy(asm: Array[RvAsm]) -> Array[RvAsm] {
    let result = [];
    for i = 0; i < asm.length(); i = i + 1 {
    
    match asm[i] {
    Mv(a, b) => {
        // If "a" is global, then this is initialization of a global variable
        if (is_fake(a) && @closure.glob.val.contains(real(a))) {
            if (is_fake(b)) {
                let f_name = real(b);

                if (type_of(f_name) == Unit) {
                    continue;
                }

                // b is global as well
                // must make it *a = *b
                if (@closure.glob.val.contains(f_name)) {
                    let temp = fake(Ptr);
                    let b = fake(type_of(f_name));
                    result.push(La(temp, f_name.to_string()));
                    result.push(Ld(b, { base: temp, offset: 0 }));
                    result.push(La(temp, real(a).to_string()));
                    result.push(Sd(b, { base: temp, offset: 0 }));
                    continue;
                }
            }

            // We are loading a normal value
            // We need to do "*a = b" instead of "a = b" for values
            let temp = fake(Ptr);
            result.push(La(temp, real(a).to_string()));
            result.push(Sd(b, { base: temp, offset: 0 }));
            continue;
        }

        // If b is just normal, then nothing to do
        if (is_fake(b).not()) {
            result.push(asm[i]);
            continue;
        }
        
        // Now "a" is normal, but "b" can be something difficult to manage
    
        let f_name = real(b);
        
        if (@closure.globvar.val.contains(f_name)) {
            // We need to reform it as "a = *b"
            let temp = fake(Ptr);
            result.push(La(temp, f_name.to_string()));
            result.push(Ld(a, { base: temp, offset: 0 }));
            continue;
        }

        // Nothing special, just put it back
        result.push(asm[i]);

    }
    // Match otherwise
    _ => result.push(asm[i])
    }
    }

    return result |> tidy_fp;
}

/// If mv/ld/sd FP registers, make it correct
fn tidy_fp(asm: Array[RvAsm]) -> Array[RvAsm] {
    let result = [];
    
    for x in asm {
        match x {
            Mv(a, b) => {
                if (is_fake(a) && type_of(real(a)) == Double ||
                    is_fake(b) && type_of(real(b)) == Double) {
                        result.push(FmvD(a, b));
                        continue;
                }
            }
            Ld(r, mem) => {
                if (is_fake(r) && type_of(real(r)) == Double) {
                    result.push(Fld(r, mem));
                    continue;
                }
            }
            Sd(r, mem) => {
                if (is_fake(r) && type_of(real(r)) == Double) {
                    result.push(Fsd(r, mem));
                    continue;
                }
            }
            _ => ()
        }
        result.push(x);
    }

    return result;
}

/// Outputs labels for global variables
pub fn emit_global(logger: Logger) -> Unit {
    logger.write_string(".section .data\n");
    for x in @closure.glob.val {
        if (find_func(x).is_empty().not()) {
            continue;
        }
        
        logger.write_string("\{x.to_string()}:\n    .dword 0\n");
    }
}

/// Entry point of program
pub fn emit_main(body: @closure.Expr) -> @closure.FuncDef {
    asm.clear();

    @closure.FuncDef :: {
        name: "minimbt_main",
        old_name: @types.Name:: { name: Some("minimbt_main"), slot: -1 },
        is_closure: false,
        args: [],
        captured: [],
        body: eliminate_main_call(body)
    }
}

fn emit_fn(fun: @closure.FuncDef) -> AssemblyFunction {
    // Don't care about external functions
    if (externs.contains(fun.name._)) {
        return AssemblyFunction :: { name: "", is_extern: true, body: [] };
    }

    asm.clear();
    t_clear();
    let mut offset = 0;

    // Load arguments
    let load_arg: Array[RvAsm] = [];
    let _ = fun.args.mapi(fn (i, x) {
        match type_of(x) {
            Double => load_arg.push(FmvD(Fake(x), Farg(i)));
            _ => load_arg.push(Mv(Fake(x), Arg(i)));
        }
    });

    // Load environment (if this is a closure)
    let env = Arg(fun.args.length());
    let _ = fun.captured.mapi(fn (i, x) {
        load_arg.push(Ld(Fake(x), { base: env, offset: i * 8 + 8 }));
    });

    let ret = emit_expr(fun.body);
    let ret_reg = match type_of(real(ret)) {
        Double => Fa0
        _ => A0
    }

    let pseudobody = [
        ..load_arg,
        RvAsm::Label("\{fun.old_name}_tailrec"),
        ..asm,
        Mv(ret_reg, ret),
    ];

    if (fun.name._ == "minimbt_main") {
        // call main()
        if (t.funcs.filter(fn (x) { x.old_name.name == Some("main") }).length() > 0) {
            pseudobody.push(Call("main"));
        }

        // return 0;
        pseudobody.push(Mv(A0, Zero));
    }

    basic_regalloc(pseudobody);

    // Prologue and Epilogue is dealt with at output()
    let body = tidy(pseudobody) |> opt_loop_invariant(fun);
    t_clear();
    basic_regalloc(body);

    // Do optimizations
    let mut opt = body
            |> consolidate;
    
    for i = 0; i < 3; i = i + 1 {
        opt = opt
            |> opt_remove_identical
            |> opt_peephole_2
            |> opt_inline_var
            |> opt_remove_write
            |> opt_remove_unread
            |> opt_inline_loopvar
    }

    opt = opt
            |> opt_realloc;

    offset = t.offset;

    // Preserve registers
    let pre: Array[RvAsm] = [];
    let post: Array[RvAsm] = [];

    let mut all_used = @immut/hashset.from_array([Ra]);
    for x in opt {
        let file = reg_used(x);
        if (file.rd.is_empty().not()) {
            all_used = all_used.add(file.rd.unwrap());
        }
        if (file.rs1.is_empty().not()) {
            all_used = all_used.add(file.rs1.unwrap());
        }
        if (file.rs2.is_empty().not()) {
            all_used = all_used.add(file.rs2.unwrap());
        }
    }

    let saved = [..reg_callee_saved_list, ..freg_callee_saved_list];

    for r in all_used {
        if (saved.contains(r).not() && r != Ra) {
            continue;
        }

        if (is_intreg(r)) {
            pre.push(Sd(r, { base: Sp, offset: offset }));
            post.push(Ld(r, { base: Sp, offset: offset }));
        } else {
            pre.push(Fsd(r, { base: Sp, offset: offset }));
            post.push(Fld(r, { base: Sp, offset: offset }));
        }
        offset += 8;
    }
    
    // If we are using temporary registers, t0 - t7
    // then preserve them before any calls
    let called = [];
    let mut temp_used: @immut/hashset.T[Reg] = @immut/hashset.T::new();
    let tmp_list = [..reg_temp_list, ..freg_temp_list];
    for x in opt {
        let file = reg_used(x);
        if (file.rd.is_empty().not() && tmp_list.contains(file.rd.unwrap())) {
            temp_used = temp_used.add(file.rd.unwrap());
        }
        if (file.rs1.is_empty().not() && tmp_list.contains(file.rs1.unwrap())) {
            temp_used = temp_used.add(file.rs1.unwrap());
        }
        if (file.rs2.is_empty().not() && tmp_list.contains(file.rs2.unwrap())) {
            temp_used = temp_used.add(file.rs2.unwrap());
        }
        match x {
            Call(_) | Jalr(_) => {
                let tpre = [];
                let tpost = [];
                let _ = Array::from_iter(temp_used.iter()).mapi(fn (i, r) {
                    if (is_intreg(r)) {
                        tpre.push(Sd(r, { base: Sp, offset: offset + i * 8 }));
                        tpost.push(Ld(r, { base: Sp, offset: offset + i * 8 }));
                    } else {
                        tpre.push(Fsd(r, { base: Sp, offset: offset + i * 8 }));
                        tpost.push(Fld(r, { base: Sp, offset: offset + i * 8 }));
                    }
                });
                called.append(tpre);
                called.push(x);
                called.append(tpost);
            }
            _ => called.push(x);
        }
    }

    offset += 8 * temp_used.size();

    let full_body = [
        ..pre,
        ..called,
        ..post
    ];

    offset = (offset.to_double() / 16.0).ceil().to_int() * 16;

    AssemblyFunction :: {
        name:
            // We also want entry point to be unmodified
            if (["minimbt_main", "main"].contains(fun.name._)) {
                fun.name._
            } else {
                fun.old_name.to_string()
            },
        is_extern: externs.contains(fun.name._),
        body: [
            Addi(Sp, Sp, -offset),
            ..full_body,
            Addi(Sp, Sp, offset),
            Ret
        ]
    }
}

pub fn emit(program: @closure.Program) -> Array[AssemblyFunction] {
    t.funcs = program.fundefs.copy();

    t.funcs.push(emit_main(program.body));

    let arr = t.funcs.map(emit_fn);

    t_clear();
    return arr;
}


pub struct AssemblyFunction {
    name : String
    is_extern: Bool
    body : Array[RvAsm]
}

pub fn AssemblyFunction::output(
    self : AssemblyFunction,
    logger : Logger
) -> Unit {

    // We handle these external functions elsewhere
    if (self.is_extern) {
        return;
    }

    let name = self.name;
    if (name == "minimbt_main") {
        logger.write_string(".global \{name}\n")
    }
    logger.write_string("\{name}:\n")

    for asm in self.body {
        Show::output(asm, logger)
        logger.write_string("\n")
    }
}
