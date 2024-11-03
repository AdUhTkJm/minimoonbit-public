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
    mut first_used: Map[@typing.Name, Int]

    // The first instruction where a register is read from
    mut last_used: Map[@typing.Name, Int]

    // The register for each name in IR
    mut regs: Map[@typing.Name, Reg]
    
    // Which name occupies the register?
    mut occupy: Map[Reg, @typing.Name]

    // Temporary register count (for intermediate results)
    mut rcnt: Int

    // Label count (for if-else, while etc.)
    mut labelcount: Int

    // All functions
    mut funcs: Array[@closure.FuncDef]

    // All register used in a function
    mut all_used: @immut/sorted_set.T[Reg]
}

fn T::new() -> T {
    T :: {
        offset: 0,
        first_used: Map::new(),
        last_used: Map::new(),
        regs: Map::new(),
        occupy: Map::new(),
        rcnt: 1000000,
        labelcount: 0,
        funcs: [],
        all_used: @immut/sorted_set.T::new(),
    }
}

fn t_clear() -> Unit {
    t.offset = 0;
    t.occupy = Map::new();
    t.first_used = Map::new();
    t.last_used = Map::new();
    t.all_used = @immut/sorted_set.T::new();
    t.regs = Map::new();
}


pub let t: T = T::new();


fn reg(r: @typing.Name) -> Unit {
    for z in reg_allocatable_list {
        // z is used after this instruction, so can't reuse
        if (t.occupy.contains(z) && t.last_used[t.occupy[z].unwrap()] > t.first_used[r]) {
            continue;
        }

        t.occupy[z] = r;
        t.regs[r] = z;
        t.all_used = t.all_used.add(z);
        
        return;
    }
    
    // Spill
    t.regs[r] = Spilt(t.offset);
    t.offset += 8;
}

// Produce a fake register
fn fake() -> Reg {
    let z = Fake(@typing.Name::slot_only(t.rcnt));
    t.rcnt += 1;
    z
}

fn find_func(a: @typing.Name) -> Option[@closure.FuncDef] {
    for f in t.funcs {
        if (f.old_name == a) {
            return Some(f);
        }
    }
    None
}

// rd is the register written to, rs1 and rs2 are the ones read from
struct RegFile {
    rd: Option[Reg]
    rs1: Option[Reg]
    rs2: Option[Reg]
}

fn reg_used(asm: RvAsm) -> RegFile {
    match asm {
        Add(rd, rs1, rs2) |
        Sub(rd, rs1, rs2) |
        Xor(rd, rs1, rs2) |
        Or(rd, rs1, rs2) |
        And(rd, rs1, rs2) |
        Sll(rd, rs1, rs2) |
        Srl(rd, rs1, rs2) |
        Sra(rd, rs1, rs2) |
        Slt(rd, rs1, rs2) |
        Sltu(rd, rs1, rs2) => { rd : Some(rd), rs1 : Some(rs1), rs2 : Some(rs2) }

        Addi(rd, rs1, _) |
        Xori(rd, rs1, _) |
        Ori(rd, rs1, _) |
        Andi(rd, rs1, _) |
        Slli(rd, rs1, _) |
        Srli(rd, rs1, _) |
        Srai(rd, rs1, _) |
        Slti(rd, rs1, _) |
        Sltiu(rd, rs1, _) => { rd : Some(rd), rs1 : Some(rs1), rs2 : None }

        Lb(rd, { base: rs1, offset: _ }) |
        Lh(rd, { base: rs1, offset: _ }) |
        Lw(rd, { base: rs1, offset: _ }) |
        Ld(rd, { base: rs1, offset: _ }) |
        Lbu(rd, { base: rs1, offset: _ }) |
        Lhu(rd, { base: rs1, offset: _ }) |
        Lwu(rd, { base: rs1, offset: _ }) |
        Fld(rd, { base: rs1, offset: _ })=> { rd : Some(rd), rs1 : Some(rs1), rs2 : None }

        // Here rd is unchanged, so only a read
        Sb(rd, { base: rs1, offset: _ }) |
        Sh(rd, { base: rs1, offset: _ }) |
        Sw(rd, { base: rs1, offset: _ }) |
        Sd(rd, { base: rs1, offset: _ }) |
        Fsd(rd, { base: rs1, offset: _ }) => { rd : None, rs1 : Some(rs1), rs2 : Some(rd) }

        Beq(rs1, rs2, _) |
        Bne(rs1, rs2, _) |
        Blt(rs1, rs2, _) |
        Bge(rs1, rs2, _) |
        Ble(rs1, rs2, _) |
        Bgt(rs1, rs2, _) |
        Bltu(rs1, rs2, _) |
        Bgeu(rs1, rs2, _) => { rd : None, rs1 : Some(rs1), rs2 : Some(rs2) }
        
        Mul(rd, rs1, rs2) |
        Mulw(rd, rs1, rs2) |
        Mulh(rd, rs1, rs2) |
        Mulhsu(rd, rs1, rs2) |
        Mulhu(rd, rs1, rs2) |
        Div(rd, rs1, rs2) |
        Divw(rd, rs1, rs2) |
        Divu(rd, rs1, rs2) |
        Rem(rd, rs1, rs2) |
        Remw(rd, rs1, rs2) |
        Remu(rd, rs1, rs2) |
        FaddD(rd, rs1, rs2) |
        FsubD(rd, rs1, rs2) |
        FmulD(rd, rs1, rs2) |
        FeqD(rd, rs1, rs2) |
        FleD(rd, rs1, rs2) |
        FdivD(rd, rs1, rs2) => { rd : Some(rd), rs1 : Some(rs1), rs2 : Some(rs2) }

        La(rd, _) |
        Li(rd, _) => { rd : Some(rd), rs1 : None, rs2 : None }

        Neg(rd, rs1) |
        FnegD(rd, rs1) |
        FmvD(rd, rs1) |
        FmvDX(rd, rs1) |
        FmvXD(rd, rs1) |
        Mv(rd, rs1) => { rd : Some(rd), rs1 : Some(rs1), rs2 : None }

        Nop | Ecall | J(_) | Call(_) | Tail(_) | Ret | Label(_) | Comment(_)
            => { rd : None, rs1 : None, rs2 : None }
        
        Jalr(rs1) | Jr(rs1) => { rd : None, rs1 : Some(rs1), rs2 : None }
    }
}

fn real(reg: Option[Reg]) -> @typing.Name {
    match reg {
        Some(Fake(name)) => name
        _ => @util.die("non-fake")
    }
}

fn is_fake(reg: Option[Reg]) -> Bool {
    match reg {
        Some(Fake(_)) => true
        _ => false
    }
}

fn visited(reg: Option[Reg]) -> Bool {
    match reg {
        Some(Fake(name)) => t.first_used.contains(name)
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

fn regalloc(asm: Array[RvAsm], tidy: Bool) -> Unit {
    let to_alloc: Array[@typing.Name] = [];

    // Record all assigned registers
    // Find the first and last times where they are accessed
    for i = 0; i < asm.length(); i = i + 1 {
        let used = reg_used(asm[i]);
        if (is_fake(used.rd) && visited(used.rd).not()) {
            store_first(used.rd, i);
            to_alloc.push(real(used.rd));
        }
        store_last(used.rs1, i);
        store_last(used.rs2, i);
    }

    // After tidy(), remove unused Names
    // otherwise their last_used won't exist and makes reg() fail to work
    if (tidy) {
        let no_use: Array[@typing.Name] = [];
        for x in to_alloc {
            if (t.last_used.contains(x).not()) {
                no_use.push(x);
            }
        }
        let copy = asm.copy();
        asm.clear();
        for x in copy {
            let used = reg_used(x);
            if (is_fake(used.rd) && no_use.contains(real(used.rd))) {
                continue;
            }
            asm.push(x);
        }
    }


    to_alloc.sort_by(fn (a, b) { t.first_used[a].unwrap() - t.first_used[b].unwrap(); });
    for r in to_alloc {
        if (@closure.glob.val.contains(r)) {
            continue;
        }
        reg(r);
    }
}

// Despite its name, we will actually substitute for a call to init()
// if init() is present
// Because init() must be called earlier than main()
pub fn eliminate_main_call(expr: @closure.Expr) -> @closure.Expr {
    match expr {
        Let(a, val, w) => {
            // The final command of body will be a call to main()
            // So instead of making it a closure (in tidy())
            // we will directly compile it into a call
            match val {
                Var({ name: Some("main"), .. }) => Unit
                    
                _ => Let(a, val, eliminate_main_call(w))
            }
        }
        _ => @util.die("Unexpected global \{expr}");
    }
}

// Return value: where the result of this expression is stored
fn emit_expr(expr: @closure.Expr) -> Reg {
    match expr {
        Unit => A0
        Var(x) | FVar(x) => Fake(x)
        Int(x) => {
            let r = fake();
            asm.push(Li(r, x.to_string()));
            r;
        }
        Double(x) => {
            let r = fake();
            asm.push(Li(r, x.reinterpret_as_i64().to_string()));
            r;
        }
        Add(a, b) => {
            let r = fake();
            asm.push(Add(r, Fake(a), Fake(b)));
            r;
        }
        Sub(a, b) => {
            let r = fake();
            asm.push(Sub(r, Fake(a), Fake(b)));
            r;
        }
        Div(a, b) => {
            let r = fake();
            asm.push(Div(r, Fake(a), Fake(b)));
            r;
        }
        Mul(a, b) => {
            let r = fake();
            asm.push(Mul(r, Fake(a), Fake(b)));
            r;
        }
        FAdd(a, b) => {
            let r = fake();
            asm.push(FmvDX(Ft1, Fake(a)));
            asm.push(FmvDX(Ft2, Fake(b)));
            asm.push(FaddD(Ft1, Ft1, Ft2));
            asm.push(FmvXD(r, Ft1));
            r;
        }
        FSub(a, b) => {
            let r = fake();
            asm.push(FmvDX(Ft1, Fake(a)));
            asm.push(FmvDX(Ft2, Fake(b)));
            asm.push(FsubD(Ft1, Ft1, Ft2));
            asm.push(FmvXD(r, Ft1));
            r;
        }
        FDiv(a, b) => {
            let r = fake();
            asm.push(FmvDX(Ft1, Fake(a)));
            asm.push(FmvDX(Ft2, Fake(b)));
            asm.push(FdivD(Ft1, Ft1, Ft2));
            asm.push(FmvXD(r, Ft1));
            r;
        }
        FMul(a, b) => {
            let r = fake();
            asm.push(FmvDX(Ft1, Fake(a)));
            asm.push(FmvDX(Ft2, Fake(b)));
            asm.push(FmulD(Ft1, Ft1, Ft2));
            asm.push(FmvXD(r, Ft1));
            r;
        }
        FNeg(a) => {
            let r = fake();
            asm.push(FmvDX(Ft1, Fake(a)));
            asm.push(FnegD(Ft1, Ft1));
            asm.push(FmvXD(r, Ft1));
            r;
        }
        Eq(a, b) => {
            let r = fake();
            asm.push(Xor(r, Fake(a), Fake(b)));
            // set less than immediate, unsigned
            // r = (r < 1u ? 1 : 0)
            asm.push(Sltiu(r, r, 1));
            r;
        }
        Le(a, b) => {
            let r = fake();
            // set less than
            // r = (b < a ? 1 : 0)
            asm.push(Slt(r, Fake(b), Fake(a)));
            asm.push(Xori(r, r, 1));
            r;
        }
        Neg(a) => {
            let r = fake();
            asm.push(Sub(r, Zero, Fake(a)));
            r;
        }
        BNeg(a) => {
            let r = Fake(a);
            asm.push(Xori(r, r, 1));
            r;
        }
        ArrayGet(x, i) => {
            let r = fake();
            // r = *(x + (i << 3));
            asm.push(Slli(r, Fake(i), 3));
            asm.push(Add(r, r, Fake(x)));
            asm.push(Ld(r, { base: r, offset: 0 }));
            r;
        }
        ArrayPut(x, i, val) => {
            let r = fake();
            // *(x + (i << 3)) = val;
            asm.push(Slli(r, Fake(i), 3));
            asm.push(Add(r, r, Fake(x)));
            asm.push(Sd(Fake(val), { base: r, offset: 0 }));
            A0;
        }
        MakeTuple(arr) => {
            let r = fake();
            // Allocate an array for the tuple
            asm.push(Li(A0, (8 * arr.length()).to_string()));
            asm.push(Call("minimbt_create_ptr_array"));
            // Put everything into the array
            let _ = arr.mapi(fn (i, x) {
                asm.push(Sd(Fake(x), { base: A0, offset: i * 8 }));
            });
            // Record the array address
            asm.push(Mv(r, A0));
            r;
        }
        IfEq(a, b, body, otherwise) => {
            let l_else = "else_\{t.labelcount}";
            let end = "end_\{t.labelcount}";
            t.labelcount += 1;

            let r = fake();

            asm.push(Bne(Fake(a), Fake(b), l_else));
            asm.push(Mv(r, emit_expr(body)));
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

            let r = fake();
            asm.push(Bgt(Fake(a), Fake(b), l_else));
            asm.push(Mv(r, emit_expr(body)));
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
            ignore(arr.mapi(fn (i, x) {
                asm.push(Ld(Fake(x), { base: Fake(val), offset: i * 8 }));
            }));
            emit_expr(w);
        }
        CallExternal(name, args) => {
            if (args.length() != 0) {
                asm.push(Mv(A0, Fake(args[0])));
            }

            // Only create_**_array methods need 2 arguments
            if (name._.ends_with("_array")) {
                asm.push(Mv(A1, Fake(args[1])));
            }
            asm.push(Call(name._));
            A0
        }
        Call(name, args) => {
            let _ = args.mapi(fn (i, x) {
                asm.push(Mv(Arg(i), Fake(x)));
            });

            match @knf.value_of(name) {
                Some(Unknown) | None => {
                    // We don't know this function, have to call a closure for this

                    // Remember:
                    // struct Closure { void* (*func)(void*); void* env; };
                    let env = fake();
                    let func = fake();
                    asm.push(Ld(func, { base: Fake(name), offset: 0 }));
                    asm.push(Ld(env, { base: Fake(name), offset: 8 }));

                    // Also pass environment into function
                    asm.push(Mv(Arg(args.length()), env));
                    
                    // Do the call
                    asm.push(Jalr(func));
                    A0
                }
                Some(Fun(x)) => {
                    let fi = t.funcs.search_by(fn (z) { z.old_name == x });
                    let func = t.funcs[fi.unwrap()];
                    if (func.is_closure) {
                        // For closure, we still need to extract the environment
                        let env = fake();
                        asm.push(Ld(env, { base: Fake(name), offset: 8 }));
                        asm.push(Mv(Arg(args.length()), env));
                    }
                    // Direct call, since we know what function this is
                    asm.push(Call(name_fn(x)));
                    A0
                }
                _ => @util.die("Internal error: calling non-function in emit_expr()")
            }
        }
        // Call a tail recursive function
        CallTailRec(name, args) => {
            // No need to load a closure again
            // Just do the call
            let _ = args.mapi(fn (i, x) {
                ignore(i); ignore(x);
            //    asm.push(Mv(Arg(i), Fake(x)));
            });

            // The function we are referring to
            let f = match @knf.delete_refer(@knf.e.value[name].unwrap()) {
                Fun(x) => x
                _ => @util.die("Misbehaved tail recursion; check optimization.mbt")
            }
            asm.push(J("\{f}_tailrec"));
            A0
        }
        ExternalArray(_) => @util.die("External array not supported")
    }
}

fn weak_eq(a: Reg, b: Reg) -> Bool {
    match (a, b) {
        (Fake(x), Fake(y)) => t.regs[x] == t.regs[y]
        _ => a == b
    }
}

// Returns the name of a function
fn name_fn(f_name: @typing.Name) -> String {
    if (externs.contains(f_name.name.unwrap())) {
        f_name.name.unwrap()
    } else {
        f_name.to_string()
    }
}

fn make_closure(f_name: @typing.Name, target: Reg) -> Array[RvAsm] {
    let result = [];
    let args: Array[(@typing.Name, Int)] = [];
    let mut offset = 0;
    let f = find_func(f_name).unwrap();

    // to_string() will differentiate all local functions with same name
    // But we don't want it for external functions
    // otherwise we will get print_int_2 rather than print_int
    let name = name_fn(f_name);
    for z in f.captured {
        args.push((z, offset));
        offset += 8;
    }

    // Closure is compiled as:

    // struct Closure { void* (*func)(void*); void* env;  };
    // This has size 16

    // We save a Closure* in register 'f_name',
    // which currently holds a function pointer
    if (args.length() != 0) {
        let t = fake();

        // void* a0 = malloc(env_size);
        result.push(Li(A0, offset.to_string()));
        result.push(Call("minimbt_malloc"));
        result.push(Mv(t, A0));
        
        // Copy environment to space at a0
        let _ = args.mapi(fn (i, x) {
            result.push(Sd(Fake(x.0), { base: A0, offset: i * 8 }));
        });

        // void* a0 = malloc(16);
        result.push(Li(A0, "16"));
        result.push(Call("minimbt_malloc"));

        // Save Closure in memory
        result.push(La(target, name));
        result.push(Sd(target, { base: A0, offset: 0 }));
        result.push(Sd(t, { base: A0, offset: 8 }));
        result.push(Mv(target, A0));
    } else {
        // void* a0 = malloc(16);
        result.push(Li(A0, "16"));
        result.push(Call("minimbt_malloc"));

        // Save Closure in memory, but ignore env part
        result.push(La(target, name));
        result.push(Sd(target, { base: A0, offset: 0 }));
        result.push(Mv(target, A0));
    }
    return result;
}

// If referencing global things, make it correct
pub fn tidy(asm: Array[RvAsm]) -> Array[RvAsm] {
    let result = [];
    for i = 0; i < asm.length(); i = i + 1 {
    
    match asm[i] { Mv(a, b) => {
        let w = Some(a);
        let r = Some(b);
        
        // If "a" is global, then this is initialization of a global variable
        if (is_fake(w) && @closure.glob.val.contains(real(w))) {
            if (is_fake(r)) {
                let f_name = real(r);

                // We are loading a function into "a"
                // Make it a closure
                if (find_func(f_name).is_empty().not()) {
                    let closure = fake();
                    let temp = fake();
                    result.append(make_closure(f_name, closure)); 
                    result.push(La(temp, a.to_string()));
                    result.push(Sd(closure, { base: temp, offset: 0 }));
                    continue;
                }
            }

            // We are loading a normal value
            // We need to do "*a = b" instead of "a = b" for values
            let temp = fake();
            result.push(La(temp, a.to_string()));
            result.push(Sd(b, { base: temp, offset: 0 }));
            continue;
        }

        // If b is just normal, then nothing to do
        if (is_fake(r).not()) {
            result.push(asm[i]);
            continue;
        }
        

        // Now "a" is normal, but "b" can be something difficult to manage
    
        // If b is a function, we need to make it a closure
        let f_name = real(r);

        if (find_func(f_name).is_empty().not()) {
            // Note that this can very much be "mv a0, b"
            // And we use a0 intensively, so have to take care
            let target = if (weak_eq(a, A0)) { fake() } else { a };

            result.append(make_closure(f_name, target));
            continue;
        }
        
        // This is global, but not a function
        // Hence b must be a global variable
        if (@closure.glob.val.contains(f_name)) {
            // We need to reform it as "a = *b"
            let temp = fake();
            result.push(La(temp, f_name.to_string()));
            result.push(Ld(a, { base: temp, offset: 0 }));
            continue;
        }

        // Nothing special, just put it back
        result.push(asm[i]);

    }
        // Match ...
        _ => result.push(asm[i])
        }
    }
    return result;
}

fn remove_unused(body: Array[RvAsm]) -> Unit {
    let mut i = 0;
    let asm = body.copy();
    body.clear();
    while (i < asm.length()) {
        match asm[i] {
            Addi(a, b, 0) => {
                // Remove "addi a, a, 0"
                if (weak_eq(a, b).not()) {
                    body.push(asm[i]);
                }
            }
            Mv(a, b) => {
                // Remove "mv a, a"
                if (weak_eq(a, b).not()) {
                    body.push(asm[i]);
                }
            }
            _ => body.push(asm[i])
        }
        i += 1;
    }
}

// Outputs labels for global variables
pub fn emit_global(logger: Logger) -> Unit {
    logger.write_string(".section .data\n");
    for x in @closure.glob.val {
        if (find_func(x).is_empty().not()) {
            continue;
        }
        
        logger.write_string("\{x.to_string()}:\n    .dword 0\n");
    }
}

// Entry point of program
pub fn emit_main(body: @closure.Expr) -> @closure.FuncDef {
    asm.clear();

    @closure.FuncDef :: {
        name: "minimbt_main",
        old_name: @typing.Name:: { name: Some("minimbt_main"), slot: -1 },
        is_closure: false,
        args: [],
        captured: [],
        body: eliminate_main_call(body)
    }
}

fn emit_fn(fun: @closure.FuncDef) -> AssemblyFunction {
    asm.clear();
    t_clear();
    let ret = emit_expr(fun.body);
    let mut offset = 0;

    // Load arguments
    let load_arg: Array[RvAsm] = [];
    let _ = fun.args.mapi(fn (i, x) {
        load_arg.push(Mv(Fake(x), Arg(i)));
    });

    // Load environment (if this is a closure)
    let env = Arg(fun.args.length());
    let _ = fun.captured.mapi(fn (i, x) {
        load_arg.push(Ld(Fake(x), { base: env, offset: i * 8 }));
    });


    let pseudobody = [
        RvAsm::Label("\{fun.old_name}_tailrec"),
        ..load_arg,
        ..asm,
        Mv(A0, ret),
    ];

    if (fun.name._ == "minimbt_main") {
        // If there is init(), then call init() first
        if (t.funcs.filter(fn (x) { x.old_name.name == Some("init") }).length() > 0) {
            pseudobody.push(Call("init"));
        }

        // Then call main()
        if (t.funcs.filter(fn (x) { x.old_name.name == Some("main") }).length() > 0) {
            pseudobody.push(Call("main"));
        }
    }


    regalloc(pseudobody, false);

    // Prologue and Epilogue is dealt with at output()
    let body = tidy(pseudobody);
    t_clear();
    regalloc(body, true);

    let opt = opt_remove_useless(body);
    t_clear();
    regalloc(opt, true);

    offset = t.offset;

    // Preserve registers
    let pre: Array[RvAsm] = [];
    let post: Array[RvAsm] = [];

    for r in [Ra, ..t.all_used] {
        pre.push(Sd(r, { base: Sp, offset: offset }));
        post.push(Ld(r, { base: Sp, offset: offset }));
        offset += 8;
    }

    let full_body = [
        ..pre,
        ..opt,
        ..post
    ];
    remove_unused(full_body);

    offset = (offset.to_double() / 16.0).ceil().to_int() * 16;

    AssemblyFunction :: {
        name:
            // We also want entry point to be unmodified
            if (["minimbt_main", "main", "init"].contains(fun.name._)) {
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
        ],
        regs: Map::from_iter(t.regs.iter()),
    }
}

pub fn emit(program: @closure.Program) -> Array[AssemblyFunction] {
    t.funcs = [..program.fundefs];

    // emit_main() relies on t.funcs to determine if there is call to init()
    t.funcs.push(emit_main(program.body));

    // Remove all captures of toplevel functions
    for f in t.funcs {
        let copy = f.captured.copy();
        f.captured.clear();

        for x in copy {
            if (t.funcs.fold(~init = false, fn (found, z) { found || z.old_name == x }).not()) {
                f.captured.push(x);
            }
        }
    };

    let arr = t.funcs.map(emit_fn);

    t_clear();
    return arr;
}

// Removes useless instructions
// If a register is written twice without any read in between, the first write can be ignored
fn opt_remove_useless(body: Array[RvAsm]) -> Array[RvAsm] {
    fn defake(reg: Reg) -> Reg {
        match reg {
            Fake(name) => match t.regs[name] {
                Some(w) => w
                None => Spilt(9) //@util.die("Regalloc failed! \{reg}")
            }
            z => z
        }
    }

    let last_read: Map[Reg, Int] = Map::new();
    let last_written: Map[Reg, Int] = Map::new();
    let mut used_labels: @immut/hashset.T[Label] = @immut/hashset.T::new();
    let mut to_delete: @immut/hashset.T[Int] = @immut/hashset.T::new();

    fn store_write(key: Option[Reg], v: Int) -> Unit {
        match key {
            Some(Fake(_)) => ();
            _ => return;
        }

        let ind = defake(key.unwrap());

        if (last_written[ind].is_empty().not()) {
            let wtime = last_written[ind].unwrap();

            if (last_read.contains(ind).not() || wtime > last_read[ind].unwrap()) {
                to_delete = to_delete.add(wtime);
            }
        }

        last_written[ind] = v;
    }
    
    fn store_read(key: Option[Reg], v: Int) -> Unit {
        if (key.is_empty()) {
            return;
        }

        let ind = defake(key.unwrap());
        last_read[ind] = v;
    }

    for i = 0; i < body.length(); i = i + 1 {
        let asm = body[i];

        // Must clear for jumps
        // (No need to clear for function calls because all registers are preserved)
        match asm {
            J(label) | Bne(_, _, label) | Bgt(_, _, label) => {
                used_labels = used_labels.add(label);
                last_read.clear();
                last_written.clear();
            }
            La(_, label) => {
                used_labels = used_labels.add(label);
            }
            _ => ()
        }

        let used = reg_used(asm);
        store_read(used.rs1, i);
        store_read(used.rs2, i);
        store_write(used.rd, i);
    }

    let opt = [];
    for i = 0; i < body.length(); i = i + 1 {
        if (to_delete.contains(i)) {
            continue;
        }

        match body[i] {
            Label(x) as label => if (used_labels.contains(x)) {
                opt.push(label);
            }
            t => opt.push(t);
        }
    }

    return opt;
}

pub struct AssemblyFunction {
    name : String
    is_extern: Bool
    body : Array[RvAsm]
    mut regs: Map[@typing.Name, Reg]
}

pub fn AssemblyFunction::output(
    self : AssemblyFunction,
    logger : Logger
) -> Unit {

    // We handle these external functions elsewhere
    if (self.is_extern) {
        return;
    }

    current_func.val = self;

    let name = self.name;
    logger.write_string(".global \{name}\n")
    logger.write_string("\{name}:\n")

    for asm in self.body {
        Show::output(asm, logger)
        logger.write_string("\n")
    }
}
