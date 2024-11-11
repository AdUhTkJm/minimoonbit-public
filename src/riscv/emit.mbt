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

    // A list of external arrays
    mut externals: Map[@closure.Expr, @types.Name]

    // If any memory allocation appeared
    mut mallocked: Bool

    // If the entry point is directly on main()
    mut merged: Bool
}

fn T::new() -> T {
    T :: {
        offset: 0,
        first_used: Map::new(),
        last_used: Map::new(),
        regs: Map::new(),
        occupy: Map::new(),
        rcnt: 0,
        labelcount: 0,
        funcs: [],
        externals: Map::new(),
        mallocked: false,
        merged: false,
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


fn reg(r: @types.Name, allowed: Array[Reg]) -> Unit {
    for z in allowed {
        // z is used after this instruction, so can't reuse
        if (t.occupy.contains(z) && t.last_used[t.occupy[z].unwrap()] > t.first_used[r]) {
            continue;
        }

        t.occupy[z] = r;
        t.regs[r] = z;
        
        return;
    }
    
    // Spill
    if (typeof(r) == Double) {
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

fn typeof(name: @types.Name) -> @types.Type {
    match @knf.typing[name] {
        Some(x) => @typing.real(x)
        _ => @util.die("emit: cannot determine type of \{name}")
    }
}

fn sizeof(name: @types.Name) -> Int {
    match typeof(name) {
        Int => 4
        _ => 8
    }
}

fn has_call(asm: Array[RvAsm]) -> Bool {
    for x in asm {
        match x {
            Call(_) | Jalr(_) => return true;
            _ => ()
        }
    }
    return false;
}

/// It just scans through.
/// to deal with loops, special taken must be taken in PREVIOUS stages.
/// Updates t.regs[] to store registers.
fn basic_regalloc(asm: Array[RvAsm], allowed: Array[Reg], f_allowed: Array[Reg]) -> Unit {
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

    to_alloc.sort_by(fn (a, b) { t.first_used[a].unwrap() - t.first_used[b].unwrap(); });

    for r in to_alloc {
        if (@closure.glob.val.contains(r)) {
            continue;
        }
        reg(r, if (typeof(r) == Double) { f_allowed } else { allowed });
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
        LShift(a, i) => {
            let r = fake(Int);
            asm.push(Slli(r, Fake(a), i));
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
            if (typeof(a) == Double) {
                asm.push(FeqD(r, Fake(a), Fake(b)));
            } else {
                asm.push(Xor(r, Fake(a), Fake(b)));
                asm.push(Sltiu(r, r, 1));
            }
            r;
        }
        Le(a, b) => {
            let r = fake(Int);
            if (typeof(a) == Double) {
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
        Deref(x) => {
            let ty = match typeof(x) {
                Array(w) => w
                _ => @util.die("emit: deref non-array \{x}: \{typeof(x)}");
            }

            let result = fake(ty);

            match ty {
                Double => asm.push(Fld(result, { base: Fake(x), offset: 0 }));
                Int =>  asm.push(Lw(result, { base: Fake(x), offset: 0 }));
                _ => asm.push(Ld(result, { base: Fake(x), offset: 0 }));
            }
            result;
        }
        Save(x, val) => {
            match typeof(val) {
                Double => asm.push(Fsd(Fake(val), { base: Fake(x), offset: 0 }));
                Int => asm.push(Sw(Fake(val), { base: Fake(x), offset: 0 }));
                _ => asm.push(Sd(Fake(val), { base: Fake(x), offset: 0 }));
            }
            fake(Unit);
        }
        ArrayGet(_) | ArrayPut(_) => 
            @util.die("emit: array operations should have been translated")
        ExternalArray(const) => {
            if (const.length() == 0) {
                return fake(Unit);
            } 
            let ty: @types.Type = match const[0] {
                Int(_) => Int
                Double(_) => Double
                Fun(name) => typeof(name)
                _ => @util.die("emit: bad external array: \{const}")
            }
            let tmp = fake(Array(ty));
            if (t.externals.contains(expr)) {
                asm.push(La(tmp, t.externals[expr].unwrap().to_string()));
            } else {
                let ext = fake(Array(ty));
                t.externals[expr] = real(ext);
                asm.push(La(tmp, real(ext).to_string()));
            }
            tmp;
        }
        MakeTuple(arr) => {
            let r = fake(Tuple(arr.map(typeof)));

            // Allocate an array for the tuple
            let size = arr.fold(~init = 0, fn (total, x) { total + sizeof(x) });

            let mut offset = 0;

            // Put everything into the array
            for x in arr {
                match typeof(x) {
                    Double => asm.push(Fsd(Fake(x), { base: S9, offset: offset }));
                    Int => asm.push(Sw(Fake(x), { base: S9, offset: offset }));
                    _ => asm.push(Sd(Fake(x), { base: S9, offset: offset }));
                }
                offset += sizeof(x);
            }

            // Record the array address
            asm.push(Mv(r, S9));
            asm.push(Addi(S9, S9, size));
            t.mallocked = true;

            r;
        }
        IfEq(a, b, body, otherwise) => {
            let l_else = "else_\{t.labelcount}";
            let end = "end_\{t.labelcount}";
            t.labelcount += 1;
            
            let ty: @types.Type = match typeof(a) {
                Int => Int
                Double => Double
                _ => @util.die("emit: type error in if-eq (\{a}: \{typeof(a)})");
            };

            if (ty == Int) {
                asm.push(Bne(Fake(a), Fake(b), l_else));
            } else {
                let tmp = fake(Int);
                asm.push(FeqD(tmp, Fake(a), Fake(b)));
                asm.push(Beq(tmp, Zero, l_else));
            }
            
            let e_body = emit_expr(body);
            let r = fake(typeof(real(e_body)));

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

            let ty: @types.Type = match typeof(a) {
                Int => Int
                Double => Double
                _ => @util.die("emit: type error in if-eq (\{a}: \{typeof(a)})");
            };

            if (ty == Int) {
                asm.push(Bgt(Fake(a), Fake(b), l_else));
            } else {
                let tmp = fake(Int);
                asm.push(FleD(tmp, Fake(a), Fake(b)));
                asm.push(Beq(tmp, Zero, l_else));
            }
            
            let e_body = emit_expr(body);
            let r = fake(typeof(real(e_body)));

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
            let mut offset = 0;
            for x in arr {
                match typeof(x) {
                    Double => asm.push(Fld(Fake(x), { base: Fake(val), offset: offset }));
                    Int => asm.push(Lw(Fake(x), { base: Fake(val), offset: offset }));
                    _ => asm.push(Ld(Fake(x), { base: Fake(val), offset: offset }));
                }
                offset += sizeof(x);
            };
            emit_expr(w);
        }
        CallExternal(name, args) => {
            // The only external we used is create_**_array
            if (args.length() > 1) {
                match typeof(args[1]) {
                    Double => asm.push(FmvD(Fa0, Fake(args[1])));
                    _ => asm.push(Mv(A1, Fake(args[1])));
                }

                asm.push(Mv(A0, Fake(args[0])));
                asm.push(Call(name._));
                
                let rv = fake(Array(typeof(args[1])));
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
                match typeof(x) {
                    Double(_) => asm.push(FmvD(Farg(i), Fake(x)));
                    _ => asm.push(Mv(Arg(i), Fake(x)));
                }
            });

            asm.push(Call(name_fn(name)));

            let ret_ty = match typeof(name) {
                Fun(_, r) => r
                _ => @util.die("emit: calling non-function: \{typeof(name)}")
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

            // Used in optimization passes
            asm.push(Comment("__reload_args"));

            let _ = args.mapi(fn (i, x) {
                asm.push(Mv(Fake(f.args[i]), Fake(x)));
            });

            let _ = f.captured.map(fn (x) {
                match typeof(x) {
                    Double => asm.push(FmvD(Fake(x), Fake(x)));
                    _ => asm.push(Mv(Fake(x), Fake(x)));
                };
            });

            asm.push(J("\{f.old_name}_tailrec"));

            let ret_ty = match typeof(name) {
                Fun(_, r) => r
                _ => @util.die("emit: calling non-function: \{typeof(name)}")
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
                let result = fake(typeof(f));

                let amap = {};

                for x in ff.captured {
                    if (find_func(x).is_empty()) {
                        amap[x] = Fake(x);
                    } else {
                        amap[x] = pack(x);
                    }
                }

                let capsize = ff.captured.fold(~init = 0, fn (total, x) { total + sizeof(x) });

                asm.push(La(r, name_fn(f)));
                asm.push(Sd(r, { base: S9, offset: 0 }));

                let mut offset = 8;
                for x in ff.captured {
                    match typeof(x) {
                        Double => asm.push(Fsd(amap[x].unwrap(), { base: S9, offset: offset }));
                        Int => asm.push(Sw(amap[x].unwrap(), { base: S9, offset: offset }));
                        _ => asm.push(Sd(amap[x].unwrap(), { base: S9, offset: offset }));
                    }
                    offset += sizeof(x);
                }

                asm.push(Mv(result, S9));
                asm.push(Addi(S9, S9,(8 + capsize)));
                t.mallocked = true;

                return result;
            }
            pack(f)
        }
        CallClosure(closure, args) => {
            let f = fake(Ptr);

            asm.push(Ld(f, { base: Fake(closure), offset: 0 }));
            asm.push(Mv(Arg(args.length()), Fake(closure)));

            let _ = args.mapi(fn (i, x) {
                match typeof(x) {
                    Double(_) => asm.push(FmvD(Farg(i), Fake(x)));
                    _ => asm.push(Mv(Arg(i), Fake(x)));
                }
            });

            asm.push(Jalr(f));

            let ret_ty = match typeof(closure) {
                Fun(_, r) => r
                _ => @util.die("emit: calling non-function: \{typeof(closure)}")
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

                if (typeof(f_name) == Unit) {
                    continue;
                }

                // b is global as well
                // must make it *a = *b
                if (@closure.glob.val.contains(f_name)) {
                    let temp = fake(Ptr);
                    let b = fake(typeof(f_name));
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
                if (is_fake(a) && typeof(real(a)) == Double ||
                    is_fake(b) && typeof(real(b)) == Double) {
                        result.push(FmvD(a, b));
                        continue;
                }
            }
            Ld(r, mem) => {
                if (is_fake(r) && typeof(real(r)) == Double) {
                    result.push(Fld(r, mem));
                    continue;
                }
            }
            Sd(r, mem) => {
                if (is_fake(r) && typeof(real(r)) == Double) {
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

        // These are temporary things that we'd never use
        // External arrays are like this but we don't emit them here
        if (x.name.is_empty()) {
            continue;
        }
        
        logger.write_string("\{x.to_string()}:\n    .dword 0\n");
    }
}

pub fn emit_externals(logger: Logger) -> Unit {
    for k, v in t.externals {
        let const = match k {
            ExternalArray(arr) => arr
            _ => @util.die("emit: bad external array: \{k}")
        }
        if (const.length() == 0) {
            continue;
        }

        let ty: @types.Type = match const[0] {
            Int(_) => Int
            Double(_) => Double
            _ => @util.die("emit: bad external array: \{const}")
        }
        logger.write_string("\{v}:\n    ");
        logger.write_string(match ty {
            Int => ".word "
            Double => ".double "
            _ => ".dword "
        });

        logger.write_string(match const[0] {
            Int(x) => x.to_string()
            Double(x) => x.to_string()
            _ => @util.die("emit: bad external array: \{const}")
        });

        for x in const[1:] {
            logger.write_string(match x {
                Int(x) => ", " + x.to_string()
                Double(x) => "," + x.to_string()
                _ => @util.die("emit: bad external array: \{const}")
            });
        }
        logger.write_string("\n\n");
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
        match typeof(x) {
            Double => load_arg.push(FmvD(Fake(x), Farg(i)));
            _ => load_arg.push(Mv(Fake(x), Arg(i)));
        }
    });

    // Load environment (if this is a closure)
    let env = Arg(fun.args.length());
    let mut cap_offset = 0;
    for x in fun.captured {
        match typeof(x) {
            Double => load_arg.push(Fld(Fake(x), { base: env, offset: cap_offset + 8 }));
            Int => load_arg.push(Lw(Fake(x), { base: env, offset: cap_offset + 8 }));
            _ => load_arg.push(Ld(Fake(x), { base: env, offset: cap_offset + 8 }));
        }
        cap_offset += sizeof(x);
    };

    let ret = emit_expr(fun.body);
    let ret_reg = match typeof(real(ret)) {
        Double => Fa0
        _ => A0
    }

    let reserve = [];
    if (fun.name._ == "minimbt_main" && t.mallocked) {
        reserve.push(La(S9, "__reserved"));
    }

    let pseudobody = [
        ..reserve,
        ..load_arg,
        RvAsm::Label("\{fun.old_name}_tailrec"),
        ..asm,
        Mv(ret_reg, ret),
    ];

    if (fun.name._ == "minimbt_main") {
        if (t.merged.not() && t.funcs.filter(fn (x) { x.old_name.name == Some("main") }).length() > 0) {
            pseudobody.push(Call("main"));
        }
    }

    let mut allowed = [];
    let mut f_allowed = [];

    if (has_call(pseudobody)) {
        allowed = reg_allocatable_list;
        f_allowed = freg_allocatable_list;
    } else if (fun.is_closure.not()) {
        allowed = reg_allocatable_list_biased;
        f_allowed = freg_allocatable_list_biased;
    } else {
        for x in reg_allocatable_list_biased {
            // Otherwise this will break loading of environment
            if (reg_arg_list[fun.args.length()] != x) {
                allowed.push(x);
            }
        }
        for x in freg_allocatable_list_biased {
            if (freg_arg_list[fun.args.length()] != x) {
                f_allowed.push(x);
            }
        }
    }

    basic_regalloc(pseudobody, allowed, f_allowed);

    // Prologue and Epilogue is dealt with at output()
    let body = tidy(pseudobody)
        |> opt_loop_constant(fun)
        |> opt_loop_invariant;

    t_clear();
    basic_regalloc(body, allowed, f_allowed);
    for x in body { println(x) };

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
            |> opt_squeeze_loop
    }

    opt = opt
            |> opt_realloc;

    offset = t.offset;

    // Preserve registers
    let pre: Array[RvAsm] = [];
    let post: Array[RvAsm] = [];

    let called = has_call(opt);
    let mut all_used = @immut/hashset.new();
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

    let copy = @immut/hashset.T::from_iter(all_used.iter());
    let saved = [..reg_callee_saved_list, ..freg_callee_saved_list];

    all_used = @immut/hashset.T::new();

    for r in copy {
        if (saved.contains(r).not()) {
            continue;
        }
        all_used = all_used.add(r);
    }

    // If no registers are saved and the only call is tail call
    // (special case of tail-call optimization)
    let mut is_tail = all_used.size() == 0;
    if (is_tail && opt.length() > 0) {
        let last = opt.length() - 1;
        for x in opt[:last] {
            match x {
                Call(_) | Jalr(_) => { is_tail = false; break; }
                _ => ()
            }
        }
        match opt[last] {
            Call(_) => ()
            _ => is_tail = false;
        }

        if (is_tail) {
            match opt[last] {
                Call(l) => opt = [..opt[:last], J(l)];
                _ => ()
            }
        }
    }

    if (called && is_tail.not()) {
        all_used = all_used.add(Ra);
    }

    for r in all_used {
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
    offset = (offset.to_double() / 16.0).ceil().to_int() * 16;

    let full_body =
        if (offset > 0) {[
            Addi(Sp, Sp, -offset),
            ..pre,
            ..called,
            ..post,
            Addi(Sp, Sp, offset),
            Ret
        ]} else if (is_tail) {
            [..pre, ..called, ..post]
        } else {
            [..pre, ..called, ..post, Ret]
        }

    AssemblyFunction :: {
        name:
            // We also want entry point to be unmodified
            if (["minimbt_main", "main"].contains(fun.name._)) {
                fun.name._
            } else {
                fun.old_name.to_string()
            },
        is_extern: externs.contains(fun.name._),
        body: full_body
    }
}

pub fn emit(program: @closure.Program) -> Array[AssemblyFunction] {
    t.rcnt = @closure.t.cnt + 1;
    
    t.funcs = program.fundefs.copy();
    
    // No global variables
    // (We will always have one extra unused global variable)
    if (@closure.globvar.val.size() != 1) {
        t.funcs.push(emit_main(program.body));
    } else {
        t.merged = true;
        // No global variables:
        // just directly use main as entry
        for x in t.funcs {
            if (x.name == "main") {
                x.name = "minimbt_main";
            }
        }
    }

    let arr = t.funcs.map(emit_fn);

    t_clear();
    return arr;
}

pub fn emit_bss(logger: Logger) -> Unit {
    logger.write_string("\n\n.section .bss\n__reserved:\n    .space 1073741824");
}


pub struct AssemblyFunction {
    mut name : String
    mut is_extern: Bool
    mut body : Array[RvAsm]
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
