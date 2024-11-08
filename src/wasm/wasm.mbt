enum Wasm {
    Add(Wasm, Wasm)
    Sub(Wasm, Wasm)
    Mul(Wasm, Wasm)
    Div(Wasm, Wasm)
    Eq(Wasm, Wasm)
    Le(Wasm, Wasm)
    Xor(Wasm, Wasm)
    Var(@typing.Name)
    Memset(Int, Wasm, Wasm)
    Memget(Int, Wasm)
    DeclareLocal(@typing.Name)
    LocalSet(@typing.Name, Wasm)
    Call(Wasm)
    Ret(Wasm)
    DirectOutput(String)
}

struct WasmEnv {
    ftable: Map[@typing.Name, Int]

    fdef: Map[@typing.Name, @closure.FuncDef]

    mut counter: Int
}

pub let e: WasmEnv = WasmEnv::new();

let asm: Array[Wasm] = [];

pub fn WasmEnv::new() -> WasmEnv {
    WasmEnv :: {
        ftable: Map::new(),
        fdef: Map::new(),
        counter: 0,
    }
}

fn WasmEnv::get_fn(self: WasmEnv, name: @typing.Name) -> Int {
    match self.ftable[name] {
        Some(t) => t
        None => @util.die("No function table entry for \{name}")
    };
}

fn WasmEnv::fake(self: WasmEnv) -> @typing.Name {
    self.counter += 1;
    let name = @typing.Name::slot_only(1000000 + self.counter);
    asm.push(DeclareLocal(name));
    name;
}

pub fn Wasm::to_string(self: Wasm) -> String {
    match self {
        Add(a, b) => "(i32.add \{a} \{b})"
        Sub(a, b) => "(i32.sub \{a} \{b})"
        Mul(a, b) => "(i32.mul \{a} \{b})"
        Div(a, b) => "(i32.div \{a} \{b})"
        Eq(a, b) => "(i32.eq \{a} \{b})"
        Le(a, b) => "(i32.le_s \{a} \{b})"
        Xor(a, b) => "(i32.xor \{a} \{b})"
        Var(a) => "(local.get $\{a})"
        DeclareLocal(a) => "(local $\{a} i32)"
        LocalSet(a, val) => "(local.set $\{a} \{val})"
        Memset(offset, ptr, num) => "(i32.store offset=\{offset} \{ptr} \{num})"
        Memget(offset, ptr) => "(i32.load offset=\{offset} \{ptr})"
        Call(handle_fn) => "(call_indirect (type $_ftype) \{handle_fn})"
        Ret(x) => "(return \{x})"
        DirectOutput(x) => x
    }
}

// Decide if this is global
fn var(a: @typing.Name) -> Wasm {
    if (@closure.globvar.val.contains(a)) {
        DirectOutput("(global.get $\{a})");
    } else {
        Var(a)
    }
}

fn make_closure(name: @typing.Name, a: @typing.Name) -> Array[Wasm] {
    let result = [];
    let mem = e.fake();

    // struct Closure { int fn_handle; void* env; }

    let fun = e.fdef[name].unwrap();
    result.push(LocalSet(mem, DirectOutput("(call $minimbt_malloc (i32.const \{fun.captured.length() * 4}))")));
    ignore(fun.captured.mapi(fn (i, z) {
        if (e.ftable.contains(z)) {
            result.append(make_closure(z, a))
            result.push(Memset(i * 4, Var(mem), Var(a)));
        } else {
            result.push(Memset(i * 4, Var(mem), Var(z)));
        }
    }));

    let closure = e.fake();
    result.push(LocalSet(closure, DirectOutput("(call $minimbt_malloc (i32.const 8))")));
    result.push(Memset(0, Var(closure), DirectOutput("(i32.const \{e.get_fn(name)})")));
    result.push(Memset(4, Var(closure), Var(mem)));
    result.push(LocalSet(a, Var(closure)));
    return result;
}

// Returns the local variable where the result will be ready
fn emit_expr(expr: @closure.Expr) -> Wasm {
    match expr {
        Int(a) => 
            DirectOutput("(i32.const \{a})");
        Double(a) =>
            DirectOutput("(i32.const \{a.to_float().reinterpret_as_int()})")
        Var(a) =>
            // This is a global variable
            var(a)
        Let(a, val, w) => {
            let mut is_fn = false;
            asm.push(DeclareLocal(a));
            match val {
                // This is a function
                Var(name) => if (e.ftable.contains(name)) {
                    is_fn = true;

                    asm.append(make_closure(name, a));
                }
                _ => ()
            }

            if (is_fn.not()) {
                asm.push(LocalSet(a, emit_expr(val)));
            }
            
            emit_expr(w);
        }
        Add(a, b) => {
            let r = e.fake();
            asm.push(LocalSet(r, Add(var(a), var(b))));
            Var(r);
        }
        Sub(a, b) => {
            let r = e.fake();
            asm.push(LocalSet(r, Sub(var(a), var(b))));
            Var(r);
        }
        Mul(a, b) => {
            let r = e.fake();
            asm.push(LocalSet(r, Mul(var(a), var(b))));
            Var(r);
        }
        Div(a, b) => {
            let r = e.fake();
            asm.push(LocalSet(r, Div(var(a), var(b))));
            Var(r);
        }
        Neg(a) => {
            let r = e.fake();
            asm.push(LocalSet(r, Sub(DirectOutput("(i32.const 0)"), var(a))));
            Var(r);
        }
        Eq(a, b) => {
            let r = e.fake();
            asm.push(LocalSet(r, Eq(var(a), var(b))));
            Var(r);
        }
        Le(a, b) => {
            let r = e.fake();
            asm.push(LocalSet(r, Le(var(a), var(b))));
            Var(r);
        }
        FAdd(a, b) => {
            let r = e.fake();
            let a_ = e.fake();
            let b_ = e.fake();
            asm.push(LocalSet(a_, var(a)));
            asm.push(LocalSet(b_, var(b)));
            asm.push(LocalSet(r, 
            DirectOutput("(call $reintp_f (f64.add (call $reintp_i (local.get $\{a_})) (call $reintp_i (local.get $\{b_}))))")));
            Var(r);
        }
        FSub(a, b) => {
            let r = e.fake();
            let a_ = e.fake();
            let b_ = e.fake();
            asm.push(LocalSet(a_, var(a)));
            asm.push(LocalSet(b_, var(b)));
            asm.push(LocalSet(r, 
            DirectOutput("(call $reintp_f (f64.sub (call $reintp_i (local.get $\{a_})) (call $reintp_i (local.get $\{b_}))))")));
            Var(r);
        }
        FMul(a, b) => {
            let r = e.fake();
            let a_ = e.fake();
            let b_ = e.fake();
            asm.push(LocalSet(a_, var(a)));
            asm.push(LocalSet(b_, var(b)));
            asm.push(LocalSet(r, 
            DirectOutput("(call $reintp_f (f64.mul (call $reintp_i (local.get $\{a_})) (call $reintp_i (local.get $\{b_}))))")));
            Var(r);
        }
        FDiv(a, b) => {
            let r = e.fake();
            let a_ = e.fake();
            let b_ = e.fake();
            asm.push(LocalSet(a_, var(a)));
            asm.push(LocalSet(b_, var(b)));
            asm.push(LocalSet(r, 
            DirectOutput("(call $reintp_f (f64.div (call $reintp_i (local.get $\{a_})) (call $reintp_i (local.get $\{b_}))))")));
            Var(r);
        }
        FNeg(a) => {
            let r = e.fake();
            let a_ = e.fake();
            asm.push(LocalSet(a_, var(a)));
            asm.push(LocalSet(r, 
            DirectOutput("(call $reintp_f (f64.mul (f64.const 0) (call $reintp_i (local.get $\{a_}))))")));
            Var(r);
        }
        BNeg(a) => {
            let r = e.fake();
            asm.push(LocalSet(r, Xor(DirectOutput("(i32.const 1)"), var(a))));
            Var(r);
        }
        IfLe(a, b, body, otherwise) | IfEq(a, b, body, otherwise) => {
            let r = e.fake();
            // Push condition on the stack
            asm.push(match expr {
                IfLe(_) => Le(var(a), var(b))
                IfEq(_) => Eq(var(a), var(b))
                _ => @util.die("Impossible")
            });
            let copy = asm.copy();
            asm.clear();

            // Separate if and else blocks
            let _if = emit_expr(body);
            let locals_if = locals_of(asm);
            let block_if = nonlocals_of(asm).map(fn (x) { x.to_string() }).join("\n");
            asm.clear();

            let _else = emit_expr(otherwise);
            let locals_else = locals_of(asm);
            let block_else = nonlocals_of(asm).map(fn (x) { x.to_string() }).join("\n");
            asm.clear();

            // Restore asm
            ignore([
                ..copy,
                ..locals_if,
                ..locals_else
            ].map(fn (x) { asm.push(x) }));

            asm.push(DirectOutput("(if (then \{block_if}\n\{LocalSet(r, _if)}) (else \{block_else}\n\{LocalSet(r, _else)}))"))
            Var(r);
        }
        // No tail call optimization since we cannot easily jump
        Call(name, args) | CallTailRec(name, args) => {
            let mem = e.fake();

            // Load the closure
            asm.push(LocalSet(mem, DirectOutput("(call $minimbt_malloc (i32.const \{args.length() * 4}))")));
            ignore(args.mapi(fn (i, z) {
                asm.push(Memset(i * 4, Var(mem), var(z)));
            }));

            let handle_fn = e.fake();
            let env = e.fake();
            asm.push(LocalSet(handle_fn, Memget(0, Var(name))));
            asm.push(LocalSet(env, Memget(4, Var(name))));

            // Do the real call
            let result = e.fake();
            // The arguments cannot be passed by call_indirect;
            // they must be handed over on stack
            asm.push(Var(mem));
            asm.push(Var(env));
            asm.push(LocalSet(result, Call(Var(handle_fn))));
            Var(result);
        }
        MakeTuple(arr) => {
            let r = e.fake();
            asm.push(LocalSet(r, DirectOutput("(call $minimbt_malloc (i32.const \{4 * arr.length()}))")));
            ignore(arr.mapi(fn (i, z) {
                asm.push(Memset(i * 4, Var(r), var(z)));
            }));
            Var(r);
        }
        LetTuple(x, arr, w) => {
            ignore(x.mapi(fn (i, z) {
                asm.push(DeclareLocal(z));
                asm.push(LocalSet(z, Memget(i * 4, Var(arr))));
            }));
            emit_expr(w);
        }
        CallExternal(name, args) => {
            let r = e.fake();
            let arg = args.map(fn (x) { (Var(x).to_string() )}).join(" ");
            let mut real_name = name._;
            if (name._ == "minimbt_create_float_array") {
                real_name = "minimbt_create_ptr_array";
            }
            asm.push(LocalSet(r, DirectOutput("(call $\{real_name} \{arg})")));
            Var(r);
        }
        ArrayGet(x, i) => {
            let r = e.fake();
            asm.push(LocalSet(r, DirectOutput("(i32.load offset=0 (i32.add \{var(x)} (i32.mul (i32.const 4) \{Var(i)})))")));
            Var(r);
        }
        ArrayPut(x, i, val) => {
            asm.push(DirectOutput("(i32.store offset=0 (i32.add \{var(x)} (i32.mul (i32.const 4) \{var(i)})) \{Var(val)})"));
            DirectOutput("(i32.const 0)");
        }
        Unit => DirectOutput("(i32.const 0)")
    }
}

fn name_fn(func: @closure.FuncDef) -> String {
    if ([..@riscv.externs, "main", "minimbt_main"].contains(func.name._)) {
        func.name._
    } else {
        func.old_name.to_string()
    };
}

// Same usage as @riscv.tidy
fn tidy(asm: Array[Wasm]) -> Array[Wasm] {
    return [..locals_of(asm), ..nonlocals_of(asm)];
}

fn locals_of(asm: Array[Wasm]) -> Array[Wasm] {
    let locals = [];
    let mut declared: @immut/hashset.T[@typing.Name] = @immut/hashset.T::new();
    for x in asm {
        match x {
            DeclareLocal(a) => {
                if (declared.contains(a).not()) {
                    locals.push(x);
                }
                declared = declared.add(a);
            }
            _ => ();
        }
    }
    return locals;
}

fn nonlocals_of(asm: Array[Wasm]) -> Array[Wasm] {
    let others = [];
    for x in asm {
        match x {
            DeclareLocal(_) => ();
            _ => others.push(x);
        }
    }
    return others;
}


fn emit_fn(func: @closure.FuncDef) -> String {
    asm.clear();

    // Can't fake() here, otherwise we will have two DeclareLocal(ret)
    // (another one is emitted by Let(...))
    let ret = @typing.Name::slot_only(1000000 + e.counter);
    e.counter += 1;

    // This is to make sure return value is checked;
    // so if it is a function than we will still return legal closure
    let _ = emit_expr(Let(ret, func.body, Var(ret)));
    let name = name_fn(func);

    // Load arguments
    let load: Array[Wasm] = [];
    ignore(func.args.mapi(fn (i, x) {
        load.push(DeclareLocal(x));
        load.push(LocalSet(x, Memget(i * 4, DirectOutput("(local.get $args)"))));
    }));
    ignore(func.captured.mapi(fn (i, x) {
        load.push(DeclareLocal(x));
        load.push(LocalSet(x, Memget(i * 4, DirectOutput("(local.get $env)"))));
    }));

    let tidied = tidy([
        ..load,
        ..asm,
        Ret(Var(ret))
    ]);
    let ty =
        if (["minimbt_main", "main"].contains(name)) {
            ""
        } else {
            "(type $_ftype) (param $args i32) (param $env i32)"
        }

    let result = tidied.map(fn (x) { x.to_string() }).join("\n");
    return "(func $\{name} \{ty} (result i32)\n\{result})"
}

// Prepare all external functions
fn wrappers() -> String {
    return "(import \"moonbit\" \"memory\" (memory $__memory 10))\n(import \"moonbit\" \"minimbt_malloc\" (func $minimbt_malloc (param i32) (result i32)))\n(import \"moonbit\" \"minimbt_print_int\" (func $minimbt_print_int (param i32)))\n(import \"moonbit\" \"minimbt_print_char\" (func $minimbt_print_char (param i32)))\n(import \"moonbit\" \"minimbt_print_endline\" (func $minimbt_print_endline))\n(import \"moonbit\" \"minimbt_read_int\" (func $minimbt_read_int (result i32)))\n(import \"moonbit\" \"minimbt_read_char\" (func $minimbt_read_char (result i32)))\n(import \"moonbit\" \"minimbt_create_ptr_array\" (func $minimbt_create_ptr_array (param i32) (param i32) (result i32)))\n(import \"moonbit\" \"minimbt_int_of_float\" (func $minimbt_int_of_float (param f64) (result i32)))\n(import \"moonbit\" \"minimbt_float_of_int\" (func $minimbt_float_of_int (param i32) (result f64)))\n(import \"moonbit\" \"minimbt_sin\" (func $minimbt_sin (param f64) (result f64)))\n(import \"moonbit\" \"minimbt_cos\" (func $minimbt_cos (param f64) (result f64)))\n(import \"moonbit\" \"minimbt_atan\" (func $minimbt_atan (param f64) (result f64)))\n(import \"moonbit\" \"minimbt_sqrt\" (func $minimbt_sqrt (param f64) (result f64)))\n(import \"moonbit\" \"minimbt_abs_float\" (func $minimbt_abs_float (param f64) (result f64)))\n(import \"moonbit\" \"minimbt_floor\" (func $minimbt_floor (param f64) (result f64)))\n\n(func $print_int (type $_ftype) (param $args i32) (param $env i32) (result i32)\n(call $minimbt_print_int (i32.load offset=0 (local.get $args)))\n(return (i32.const 0)))\n\n(func $print_char (type $_ftype) (param $args i32) (param $env i32) (result i32)\n(call $minimbt_print_char (i32.load offset=0 (local.get $args)))\n(return (i32.const 0)))\n\n(func $read_int (type $_ftype) (param $args i32) (param $env i32) (result i32)\n(return (call $minimbt_read_int)))\n\n(func $read_char (type $_ftype) (param $args i32) (param $env i32) (result i32)\n(return (call $minimbt_read_char)))\n\n(func $print_endline (type $_ftype) (param $args i32) (param $env i32) (result i32)\n(call $minimbt_print_endline)\n(return (i32.const 0)))\n\n(func $reintp_f (param $f f64) (result i32)\n(return (i32.reinterpret_f32 (f32.demote_f64 (local.get $f)))))\n\n(func $reintp_i (param $i i32) (result f64)\n(return (f64.promote_f32 (f32.reinterpret_i32 (local.get $i)))))\n\n(func $sin (type $_ftype) (param $args i32) (param $env i32) (result i32)\n(return (call $reintp_f (call $minimbt_sin (call $reintp_i (i32.load offset=0 (local.get $args)))))))\n\n(func $cos (type $_ftype) (param $args i32) (param $env i32) (result i32)\n(return (call $reintp_f (call $minimbt_cos (call $reintp_i (i32.load offset=0 (local.get $args)))))))\n\n(func $atan (type $_ftype) (param $args i32) (param $env i32) (result i32)\n(return (call $reintp_f (call $minimbt_atan (call $reintp_i (i32.load offset=0 (local.get $args)))))))\n\n(func $sqrt (type $_ftype) (param $args i32) (param $env i32) (result i32)\n(return (call $reintp_f (call $minimbt_sqrt (call $reintp_i (i32.load offset=0 (local.get $args)))))))\n\n(func $floor (type $_ftype) (param $args i32) (param $env i32) (result i32)\n(return (call $reintp_f (call $minimbt_floor (call $reintp_i (i32.load offset=0 (local.get $args)))))))\n\n(func $abs_float (type $_ftype) (param $args i32) (param $env i32) (result i32)\n(return (call $reintp_f (call $minimbt_abs_float (call $reintp_i (i32.load offset=0 (local.get $args)))))))\n\n(func $int_of_float (type $_ftype) (param $args i32) (param $env i32) (result i32)\n(return (call $minimbt_int_of_float (call $reintp_i (i32.load offset=0 (local.get $args))))))\n\n(func $truncate (type $_ftype) (param $args i32) (param $env i32) (result i32)\n(return (call $minimbt_int_of_float (call $reintp_i (i32.load offset=0 (local.get $args))))))\n\n(func $float_of_int (type $_ftype) (param $args i32) (param $env i32) (result i32)\n(return (call $reintp_f (call $minimbt_float_of_int (i32.load offset=0 (local.get $args))))))\n";
}

fn emit_main(body: @closure.Expr) -> String {
    asm.clear();

    fn do_emit(expr: @closure.Expr) {
        match expr {
            Let(a, val, w) => {
                let r = emit_expr(val);
                asm.push(DirectOutput("(global.set $\{a} \{r})"));
                do_emit(w);
            }
            _ => ()
        }
    }
    do_emit(@riscv.eliminate_main_call(body));
    let tidied = tidy(asm);
    let result = tidied.map(fn (x) { x.to_string() }).join("\n");
    return "(func $minimbt_main \{result} (call $main) (return))\n";
}

fn globs() -> String {
    let arr = Array::from_iter(@closure.globvar.val.iter());
    return arr.fold(~init = "", fn (total, x) {
        "\{total}\n(global $\{x} (mut i32) (i32.const 0))"
    });
}

pub fn process(program: @closure.Program) -> String {
    let funcs = program.fundefs.copy();

    for i = 0; i < funcs.length(); i = i + 1 {
        e.ftable[funcs[i].old_name] = i;
        e.fdef[funcs[i].old_name] = funcs[i];
    }

    let f_num = funcs.length();
    let names_fn = funcs.fold(~init = "", fn (total, x) {
        "\{total} $\{name_fn(x)}"}
    );
    
    // We don't want to emit external functions
    let copy = funcs.copy();
    funcs.clear();
    for x in copy {
        if (@riscv.externs.contains(x.name._).not()) {
            funcs.push(x);
        }
    }

    let result = funcs.map(emit_fn).join("\n");

    return "(module\n" +
    "\{wrappers()}" +
    "\{globs()}" +
    "(type $_ftype (func (param i32) (param i32) (result i32)))\n" +
    "(table \{f_num} funcref)\n" +
    "(elem (i32.const 0)\{names_fn})\n" +
    "\{result}\n" +
    "\{emit_main(program.body)}\n" +
    "(start $minimbt_main)\n" +
    "(export \"minimbt_main\" (func $minimbt_main)))\n";
}