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
        all_used: @immut/sorted_set.T::new()
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
        Lwu(rd, { base: rs1, offset: _ }) => { rd : Some(rd), rs1 : Some(rs1), rs2 : None }

        // Here rd is unchanged, so only a read
        Sb(rd, _) |
        Sh(rd, _) |
        Sw(rd, _) |
        Sd(rd, _) => { rd : None, rs1 : Some(rd), rs2 : None }

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
        Remu(rd, rs1, rs2) => { rd : Some(rd), rs1 : Some(rs1), rs2 : Some(rs2) }

        La(rd, _) |
        Li(rd, _) => { rd : Some(rd), rs1 : None, rs2 : None }

        Neg(rd, rs1) |
        Mv(rd, rs1) => { rd : Some(rd), rs1 : Some(rs1), rs2 : None }

        Nop | Ecall | J(_) | Call(_) | Tail(_) | Ret | Label(_) | Comment(_)
            => { rd : None, rs1 : None, rs2 : None }
        
        Jalr(rs1) | Jr(rs1) => { rd : None, rs1 : Some(rs1), rs2 : None }

        _ => @util.die("no floating point")
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

fn regalloc(asm: Array[RvAsm]) -> Unit {
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

    to_alloc.sort_by(fn (a, b) { t.first_used[a].unwrap() - t.first_used[b].unwrap(); });
    for r in to_alloc {
        reg(r);
    }
}

// Return value: where the result of this expression is stored
fn emit_expr(expr: @closure.Expr) -> Reg {
    match expr {
        Unit => A0
        Int(x) => {
            let r = fake();
            asm.push(Li(r, x.to_string()));
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
            // r = *(x + (i << 2));
            asm.push(Slti(r, Fake(i), 2));
            asm.push(Add(r, r, Fake(x)));
            asm.push(Lw(r, { base: r, offset: 0 }));
            r;
        }
        ArrayPut(x, i, val) => {
            let r = fake();
            // *(x + (i << 2)) = val;
            asm.push(Slti(r, Fake(i), 2));
            asm.push(Add(r, r, Fake(x)));
            asm.push(Sw(Fake(val), { base: r, offset: 0 }));
            A0;
        }
        MakeTuple(arr) => {
            let r = fake();
            // Allocate an array for the tuple
            asm.push(Li(A0, (8 * arr.length()).to_string()));
            // Put everything into the array
            ignore(arr.mapi(fn (i, x) {
                asm.push(Sd(Fake(x), { base: A0, offset: i * 8 }));
            }));
            // Record the array address
            asm.push(Mv(r, A0));
            r;
        }
        IfEq(a, b, body, otherwise) => {
            let l_else = "else_\{t.labelcount}";
            let end = "end_\{t.labelcount}";
            t.labelcount += 1;

            let r = fake();

            // if (a != b) { goto else; }
            // body; goto end;
            // else { otherwise }
            // end
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
            asm.push(Bge(Fake(a), Fake(b), l_else));
            asm.push(Mv(r, emit_expr(body)));
            asm.push(J(end));
            asm.push(Label(l_else));
            asm.push(Mv(r, emit_expr(otherwise)));
            asm.push(Label(end));
            r;
        }
        Let((a, _), val, w) => {
            let rv = emit_expr(val);
            asm.push(Mv(Fake(a), rv));
            emit_expr(w);
        }
        LetTuple(arr, val, w) => {
            ignore(arr.mapi(fn (i, x) {
                asm.push(Ld(Fake(x.0), { base: Fake(val), offset: i * 8 }));
            }));
            emit_expr(w);
        }
        Var(x) => {
            Fake(x)
        }
        CallExternal(name, args) => {
            if (args.length() != 0) {
                asm.push(Mv(A0, Fake(args[0])));
            }
            asm.push(Call(name._));
            A0
        }
        Call(name, args) => {
            ignore(args.mapi(fn (i, x) {
                asm.push(Mv(Arg(i), Fake(x)));
            }));

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
        _ => @util.die("!!")
    }
}

fn weak_eq(a: Reg, b: Reg) -> Bool {
    match (a, b) {
        (Fake(x), Fake(y)) => t.regs[x] == t.regs[y]
        _ => a == b
    }
}

pub fn tidy(asm: Array[RvAsm]) -> Array[RvAsm] {
    let mut i = 0;
    let result = [];
    while (i < asm.length()) {
        match asm[i] {
            Mv(a, b) => { 
                let r = Some(b);
                // If reg() hasn't allocated, b must have never appeared as rd
                // Hence b is a function
                if (is_fake(r) && t.regs.contains(real(r)).not()) {
                    // Note that this can very much be "mv a0, ..."
                    // And we use a0 intensively, so have to take care
                    let is_a0 = weak_eq(a, A0);
                    let target = if (is_a0) { fake() } else { a };

                    let args: Array[(@typing.Name, Int)] = [];
                    let mut offset = 0;
                    let f_name = real(r);
                    let f = find_func(f_name).unwrap();
                    for z in f.captured {
                        args.push((z.0, offset));
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
                        ignore(args.mapi(fn (i, x) {
                            result.push(Sd(Fake(x.0), { base: A0, offset: i * 8 }));
                        }));

                        // void* a0 = malloc(16);
                        result.push(Li(A0, "16"));
                        result.push(Call("minimbt_malloc"));

                        // Save Closure in memory
                        result.push(La(target, f_name.name.unwrap()));
                        result.push(Sd(target, { base: A0, offset: 0 }));
                        result.push(Sd(t, { base: A0, offset: 8 }));
                        if (is_a0.not()) {
                            result.push(Mv(target, A0));
                        }
                    } else {
                        // void* a0 = malloc(16);
                        result.push(Li(A0, "16"));
                        result.push(Call("minimbt_malloc"));

                        // Save Closure in memory, but ignore env part
                        result.push(La(target, real(r).name.unwrap()));
                        result.push(Sd(target, { base: A0, offset: 0 }));
                        if (is_a0.not()) {
                            result.push(Mv(target, A0));
                        }
                    }
                } else {
                    result.push(asm[i]);
                }
            }
            _ => result.push(asm[i])
        }
        i += 1;
    }
    return result;
}

pub fn tidy_2(body: Array[RvAsm]) -> Unit {
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

fn emit_fn(fun: @closure.FuncDef) -> AssemblyFunction {
    asm.clear();
    t_clear();
    let ret = emit_expr(fun.body);
    let mut offset = 0;

    // Load arguments
    let load_arg: Array[RvAsm] = [];
    ignore(fun.args.mapi(fn (i, x) {
        load_arg.push(Mv(Fake(x.0), Arg(i)));
    }));

    if (fun.name._ != "main") {
        let env = Arg(fun.args.length());
        ignore(fun.captured.mapi(fn (i, x) {
            load_arg.push(Ld(Fake(x.0), { base: env, offset: i * 8 }));
        }));
    }


    let pseudobody = [
        ..load_arg,
        ..asm,
    ];

    regalloc(pseudobody);

    // Preserve registers
    let pre: Array[RvAsm] = [];
    let post: Array[RvAsm] = [];
    for r in [Ra, ..t.all_used] {
        if (reg_callee_saved_list.contains(r).not() && weak_eq(r, Ra).not()) {
            continue;
        }
        pre.push(Sd(r, { base: Sp, offset: offset }));
        post.push(Ld(r, { base: Sp, offset: offset }));
        offset += 8;
    }

    // Prologue and Epilogue is dealt with at output()
    let body = [
        ..pre,
        ..pseudobody,
        Mv(A0, ret),
        ..post,
    ]

    AssemblyFunction :: {
        name: if (fun.name._ == "main") { "minimbt_main" } else { fun.name._ },
        export: true,
        body: tidy(body),
        offset: offset
    }
}

pub fn emit(program: @closure.Program) -> Array[AssemblyFunction] {
    t.funcs = program.fundefs;

    // Remove all captures of toplevel functions
    ignore(t.funcs.map(fn (f) {
        let copy = f.captured.copy();
        f.captured.clear();

        for x in copy {
            if t.funcs.fold(~init = false, fn (found, z) { found || z.old_name == x.0 }).not() {
                f.captured.push(x);
            }
        }
    }));

    let arr = t.funcs.map(emit_fn);
    t_clear();
    ignore(arr.map(fn (x) { t.offset = x.offset; regalloc(x.body); x.offset = t.offset }));
    ignore(arr.map(fn (x) { tidy_2(x.body) } ));
    return arr;
}

pub struct AssemblyFunction {
    name : String
    export : Bool
    body : Array[RvAsm]
    mut offset: Int
}

pub fn AssemblyFunction::output(
    self : AssemblyFunction,
    logger : Logger
) -> Unit {
    self.offset = (self.offset.to_double() / 16.0).ceil().to_int() * 16;
    let name = self.name
    if self.export {
        logger.write_string(".global \{name}\n")
    }
    logger.write_string("\{name}:\n")

    Show::output(Addi(Sp, Sp, - self.offset), logger);
    logger.write_string("\n")
    for asm in self.body {
        Show::output(asm, logger)
        logger.write_string("\n")
    }
    Show::output(Addi(Sp, Sp, self.offset), logger);
    logger.write_string("\n")
    Show::output(Ret, logger);
}
