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

    // The environment is stored in Reg for the closure called @types.Name
    mut env_of: Map[@types.Name, Reg];
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
        env_of: Map::new(),
    }
}

fn is_closure(name: @types.Name) -> Bool {
    match type_of(name) {
        Fun(_) => true
        _ => false
    }
}

fn has_env(name: @types.Name) -> Bool {
    return t.env_of.contains(name);
}

fn get_env(name: @types.Name) -> Reg {
    if (is_closure(name).not()) {
        @util.die("emit: not closure: \{name}")
    }
    match t.env_of[name] {
        Some(x) => x
        _ => @util.die("emit: no env: \{name}")
    }
}

fn add_closure(name: @types.Name, env: Reg) -> Unit {
    t.env_of[name] = env;
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
    t.regs[r] = Spilt(t.offset);
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
fn basic_regalloc(asm: Array[RvAsm], tidy_unused: Bool) -> Unit {
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

    // After tidy(), remove unused Names
    // otherwise their last_used won't exist and makes reg() fail to work
    if (tidy_unused) {
        let no_use: Array[@types.Name] = [];
        for x in to_alloc {
            if (t.last_used.contains(x).not()) {
                no_use.push(x);
            }
        }
        let copy = asm.copy();
        asm.clear();
        for x in copy {
            let used = reg_used(x);
            if (used.rd.is_empty().not() && is_fake(used.rd.unwrap()) && no_use.contains(real(used.rd.unwrap()))) {
                continue;
            }
            asm.push(x);
        }
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
                Var({ name: Some("main"), .. }) => Unit
                    
                _ => Let(a, val, eliminate_main_call(w))
            }
        }
        Call(x, _) => if (x.name == Some("main")) { Unit } else { expr }
        _ => @util.die("Unexpected global \{expr}");
    }
}

// Return value: where the result of this expression is stored
fn emit_expr(expr: @closure.Expr) -> Reg {
    match expr {
        Unit => fake(Unit)
        Var(x) | FVar(x) => {
            if (is_closure(x) && has_env(x).not() && @closure.glob.val.contains(x).not()) {
                let r = fake(type_of(x));
                asm.append(make_closure(x, r));
                r;
            } else {
                Fake(x)
            }
        }
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
        // have to rework FP registers somehow
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
                let r = fake(Int);
                asm.push(Xor(r, Fake(a), Fake(b)));
                // set less than immediate, unsigned
                // r = (r < 1u ? 1 : 0)
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

            match ty {
                // This is an array of functions
                Fun(_) => {
                    // Unpack closure
                    let closure = fake(ty);
                    asm.push(Ld(closure, { base: r, offset: 0 }));
                    asm.push(Ld(result, { base: closure, offset: 0 }));
                    
                    let env = fake(Ptr);
                    asm.push(Ld(env, { base: closure, offset: 8 }));
                    asm.push(Mv(A1, env));
                    add_closure(real(result), env);
                }
                Double => {
                    asm.push(Fld(result, { base: r, offset: 0 }));
                }
                _ => {
                    asm.push(Ld(result, { base: r, offset: 0 }));
                }
            }
            result;
        }
        ArrayPut(x, i, val) => {
            let addr = fake(Int);
            // *(x + (i << 3)) = val;
            asm.push(Slli(addr, Fake(i), 3));
            asm.push(Add(addr, addr, Fake(x)));

            match type_of(val) {
                Fun(_) => {
                    // Pack the closure
                    let closure = pack_closure(val);

                    asm.push(Sd(closure, { base: addr, offset: 0 }));
                }
                Double => {
                    asm.push(Fsd(Fake(val), { base: addr, offset: 0 }));
                }
                _ => {
                    asm.push(Sd(Fake(val), { base: addr, offset: 0 }));
                }
            } 
            fake(Unit);
        }
        MakeTuple(arr) => {
            let r = fake(Ptr);
            let array = fake(Tuple(arr.map(type_of)));

            // Allocate an array for the tuple
            asm.push(Li(A0, (8 * arr.length()).to_string()));
            asm.push(Call("minimbt_create_ptr_array"));

            // We can't directly use a0 because it might be tampered by pack_closure()
            asm.push(Mv(array, A0));

            // Put everything into the array
            let _ = arr.mapi(fn (i, x) {
                match type_of(x) {
                    Fun(_) => {
                        // Pack the closure
                        let closure = pack_closure(x);

                        asm.push(Sd(closure, { base: array, offset: i * 8 }));
                    }
                    Double => {
                        asm.push(Fsd(Fake(x), { base: array, offset: i * 8 }));
                    }
                    _ => {
                        asm.push(Sd(Fake(x), { base: array, offset: i * 8 }));
                    }
                }
            });
            // Record the array address
            asm.push(Mv(r, array));
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
                let r = fake(Int);
                asm.push(FeqD(r, Fake(a), Fake(b)));
                asm.push(Beq(r, Zero, l_else));
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
                let r = fake(Int);
                asm.push(FleD(r, Fake(a), Fake(b)));
                asm.push(Beq(r, Zero, l_else));
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
            let name = real(rv);
            
            // If we are assigning a closure to another @types.Name
            // we must also associate the same environment
            if (is_closure(name) && has_env(name)) {
                add_closure(a, get_env(name));
            }

            asm.push(Mv(Fake(a), rv));
            emit_expr(w);
        }
        LetTuple(arr, val, w) => {
            let _ = arr.mapi(fn (i, x) {
                match type_of(x) {
                    Fun(_) => {
                        // Unpack closure
                        let closure = fake(type_of(x));
                        asm.push(Ld(closure, { base: Fake(val), offset: i * 8 }));
                        asm.push(Ld(Fake(x), { base: closure, offset: 0 }));
                        
                        let env = fake(Ptr);
                        asm.push(Ld(env, { base: closure, offset: 8 }));
                        add_closure(x, env);
                    }
                    Double => {
                        asm.push(Fld(Fake(x), { base: Fake(val), offset: i * 8 }));
                    }
                    _ => {
                        asm.push(Ld(Fake(x), { base: Fake(val), offset: i * 8 }));
                    }
                }
            });
            emit_expr(w);
        }
        CallExternal(name, args) => {
            // The only external we used is create_**_array
            if (args.length() > 1) {
                match type_of(args[1]) {
                    Fun(_) => {
                        let closure = pack_closure(args[1]);
                        asm.push(Mv(A1, closure));
                    }
                    // Note that create_float_array receives fa0 as 2nd input
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
            // Must do it before we load arguments
            // because pack_closure() tampers a0
            let closures = {};
            for x in args {
                if (is_closure(x)) {
                    let closure = pack_closure(x);
                    closures[x] = closure;
                }
            }

            match @knf.value_of(name) {
                Unknown => {
                    let _ = args.mapi(fn (i, x) {
                        match type_of(x) {
                            Fun(_) => asm.push(Mv(Arg(i), closures[x].unwrap()));
                            Double(_) => asm.push(FmvD(Farg(i), Fake(x)));
                            _ => asm.push(Mv(Arg(i), Fake(x)));
                        }
                    });

                    if (is_closure(name) && has_env(name)) {
                        asm.push(Mv(Arg(args.length()), get_env(name)));
                    }
                    asm.push(Jalr(Fake(name)));
                }
                Fun(x) => {
                    let fi = t.funcs.search_by(fn (w) { w.old_name == x }).unwrap();
                    let f = t.funcs[fi];

                    if (f.is_closure && has_env(name).not()) {
                        asm.append(make_closure(x, fake(Unit)));
                        asm.push(Mv(Arg(args.length()), A1));
                    } else if (f.is_closure) {
                        asm.push(Mv(Arg(args.length()), get_env(name)));
                    }

                    let _ = args.mapi(fn (i, x) {
                        match type_of(x) {
                            Fun(_) => asm.push(Mv(Arg(i), closures[x].unwrap()));
                            Double(_) => asm.push(FmvD(Farg(i), Fake(x)));
                            _ => asm.push(Mv(Arg(i), Fake(x)));
                        }
                    });

                    asm.push(Call(name_fn(x)));
                }
                _ => @util.die("emit: calling non-function: \{@knf.value_of(name)}")
            }

             let ret_ty = match type_of(name) {
                Fun(_, r) => r
                _ => @util.die("emit: calling non-function: \{type_of(name)}")
            }
            let rv = fake(ret_ty);
            if (is_closure(real(rv))) {
                let env = fake(Ptr);
                asm.push(Mv(env, A1));
                add_closure(real(rv), env);
            }
            asm.push(Mv(rv, match ret_ty {
                Double => Fa0
                _ => A0
            }));
            rv
        }
        CallTailRec(name, args) => {
            match @knf.value_of(name) {
                // We must know what this is to do a tail-call
                Fun(x) => {
                    let fi = t.funcs.search_by(fn (w) { w.old_name == x }).unwrap();
                    let f = t.funcs[fi];

                    let _ = args.mapi(fn (i, x) {
                        if (is_closure(x)) {
                            // This will eventually be optimized;
                            // but this assures regalloc() behaves correctly
                            asm.push(Mv(get_env(x), get_env(x)));
                        }
                        asm.push(Mv(Fake(f.args[i]), Fake(x)));
                    });

                    // Same thing here
                    let _ = f.captured.map(fn (x) {
                        match type_of(x) {
                            Fun(_) => {
                                asm.push(Mv(get_env(x), get_env(x)));
                                asm.push(Mv(Fake(x), Fake(x)));
                            }
                            Double => asm.push(FmvD(Fake(x), Fake(x)));
                            _ => asm.push(Mv(Fake(x), Fake(x)));
                        };
                    });

                    asm.push(J("\{f.old_name}_tailrec"));
                }
                _ => @util.die("emit: calling unknown function in tail-call: \{@knf.value_of(name)}")
            }

            let ret_ty = match type_of(name) {
                Fun(_, r) => r
                _ => @util.die("emit: calling non-function: \{type_of(name)}")
            }
            let rv = fake(ret_ty);
            if (is_closure(real(rv))) {
                let env = fake(Ptr);
                asm.push(Mv(env, A1));
                add_closure(real(rv), env);
            }
            asm.push(Mv(rv, match ret_ty {
                Double => Fa0
                _ => A0
            }));
            rv
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
fn name_fn(f_name: @types.Name) -> String {
    if (externs.contains(f_name.name.unwrap())) {
        "minimbt_" + f_name.name.unwrap()
    } else {
        f_name.to_string()
    }
}

// This requires that "f_name" must be the real name of a function
// It pushes the pointer to f_name into target, and places env on a1
fn make_closure(f_name: @types.Name, target: Reg) -> Array[RvAsm] {
    let result = [];
    let captured: Array[(@types.Name, Int)] = [];
    let mut offset = 0;

    if (find_func(f_name).is_empty()) {
        @util.die("unknown function: \{f_name}");
    }
    let f = find_func(f_name).unwrap();

    // to_string() will differentiate all local functions with same name
    // But we don't want it for external functions
    // otherwise we will get print_int_2 rather than print_int
    let name = name_fn(f_name);
    for z in f.captured {
        captured.push((z, offset));
        offset += 8;
    }

    // Each closure is associated with a register, storing its environment
    if (captured.length() != 0) {
        let env = fake(Ptr);

        // void* a0 = malloc(env_size);
        result.push(Li(A0, offset.to_string()));
        result.push(Call("minimbt_malloc"));
        
        // Copy environment to space at a1
        for x in captured {
            if (is_closure(x.0)) {
                // pack_closure() affects asm
                // so packing happens before make_closure() is inserted into asm
                let closure = pack_closure(x.0);

                result.push(Sd(closure, { base: A0, offset: x.1 }));
            } else {
                result.push(Sd(Fake(x.0), { base: A0, offset: x.1 }));
            }
        };

        result.push(Mv(env, A0));
        result.push(La(target, name));

        // We hope to return environment in register a1, so always put it there
        result.push(Mv(A1, A0));
        add_closure(real(target), env);
    } else {
        // No closure; just a normal function pointer
        
        result.push(La(target, name));
    }
    return result;
}

// This has side-effect of modifying global array asm[]

// packs a closure into the form
// struct Closure { void* (*ptr)(void*); void* env };
// and return it in a fake register
fn pack_closure(f_name: @types.Name) -> Reg {
    let closure = fake(type_of(f_name));
    
    asm.push(Li(A0, "16"));
    asm.push(Call("minimbt_malloc"));
    asm.push(Sd(Fake(f_name), { base: A0, offset: 0 }));

    if (has_env(f_name)) {
        let env = get_env(f_name);
        asm.push(Sd(env, { base: A0, offset: 8 }));
    }

    asm.push(Mv(closure, A0));
    return closure;
}

// If referencing global things, make it correct
fn tidy(asm: Array[RvAsm]) -> Array[RvAsm] {
    let result = [];
    for i = 0; i < asm.length(); i = i + 1 {
    
    match asm[i] { Mv(a, b) => {
        // If "a" is global, then this is initialization of a global variable
        if (is_fake(a) && @closure.glob.val.contains(real(a))) {
            if (is_fake(b)) {
                let f_name = real(b);

                if (is_closure(f_name)) {
                    // must pack
                    let temp = fake(Ptr);
                    let closure = fake(type_of(f_name));

                    result.push(Li(A0, "16"));
                    result.push(Call("minimbt_malloc"));

                    // If this is global, must first make it closure
                    // otherwise this is already available
                    if (find_func(f_name).is_empty().not()) {
                        result.append(make_closure(f_name, closure));

                        result.push(La(temp, f_name.to_string()));
                        result.push(Sd(temp, { base: A0, offset: 0 }));   
                    } else {
                        result.push(Sd(b, { base: A0, offset: 0 }));
                    }

                    if (has_env(f_name)) {
                        let env = get_env(f_name);
                        result.push(Sd(env, { base: A0, offset: 8 }));
                    }
                    result.push(Mv(closure, A0));
                    result.push(La(temp, real(a).to_string()));
                    result.push(Sd(closure, { base: temp, offset: 0 }));
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

        // Discard this for a Unit
        if (type_of(f_name) == Unit) {
            continue;
        }

        // If b is a function, we need to make it a closure
        if (find_func(f_name).is_empty().not()) {
            // Note that this can very much be "mv a0, b"
            // And we use a0 intensively, so have to take care
            let target = if (weak_eq(a, A0)) { fake(type_of(f_name)) } else { a };

            result.append(make_closure(f_name, target));
            result.push(Mv(a, target));
            continue;
        }
        
        // This is global, but not a function
        // Hence b must be a global variable
        if (@closure.glob.val.contains(f_name)) {
            // We need to reform it as "a = *b"
            let temp = fake(Ptr);
            result.push(La(temp, f_name.to_string()));
            result.push(Ld(a, { base: temp, offset: 0 }));
            if (is_closure(f_name)) {
                // Must unpack
                let env = fake(Ptr);
                result.push(Ld(env, { base: a, offset: 8 }));
                result.push(Mv(A1, env));
                result.push(Ld(a, { base: a, offset: 0 }));
                add_closure(real(a), env);
            }
            continue;
        }

        // Nothing special, just put it back
        result.push(asm[i]);

    }
        // Match ...
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
    let closures: Array[@types.Name] = [];
    let _ = fun.args.mapi(fn (i, x) {
        if (is_closure(x)) {
            closures.push(x);
        }
        match type_of(x) {
            Double => load_arg.push(FmvD(Fake(x), Farg(i)));
            _ => load_arg.push(Mv(Fake(x), Arg(i)));
        }
    });

    // Load environment (if this is a closure)
    let env = Arg(fun.args.length());
    let _ = fun.captured.mapi(fn (i, x) {
        if (is_closure(x)) {
            closures.push(x);
        }
        load_arg.push(Ld(Fake(x), { base: env, offset: i * 8 }));
    });
    
    // Unpack closures (if any)
    for packed in closures {
        let env = fake(Ptr);
        load_arg.push(Ld(env, { base: Fake(packed), offset: 8 }));
        load_arg.push(Ld(Fake(packed), { base: Fake(packed), offset: 0 }));
        t.env_of[packed] = env;
    }

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

    basic_regalloc(pseudobody, false);

    // Prologue and Epilogue is dealt with at output()
    let body = tidy(pseudobody) |> opt_loop_invariant(fun);
    t_clear();
    basic_regalloc(body, true);

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

        if (reg_all_list.contains(r)) {
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
                    if (reg_all_list.contains(r)) {
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
    logger.write_string(".global \{name}\n")
    logger.write_string("\{name}:\n")

    for asm in self.body {
        Show::output(asm, logger)
        logger.write_string("\n")
    }
}
