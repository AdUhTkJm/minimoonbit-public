fn defake(reg: Reg) -> Reg {
    match reg {
        Fake(name) => match t.regs[name] {
            Some(w) => w
            None => {
                if (type_of(name) != Unit) {
                    @util.die("emit: cannot find \{reg}")
                }
                Zero
            }
        }
        Arg(i) => reg_arg_list[i]
        Farg(i) => freg_arg_list[i]
        z => z
    }
}

fn deref(ref: Map[Reg, Reg], reg: Reg) -> Reg {
    match ref[reg] {
        Some(t) => deref(ref, t)
        None => reg
    }
}


// If a register is written twice without any read in between, the first write can be ignored
// If a label is never referenced, then it can be ignored
pub fn opt_remove_write(body: Array[RvAsm]) -> Array[RvAsm] {
    let last_read: Map[Reg, Int] = Map::new();
    let last_written: Map[Reg, Int] = Map::new();
    let mut used_labels: @immut/hashset.T[Label] = @immut/hashset.T::new();
    let mut to_delete: @immut/hashset.T[Int] = @immut/hashset.T::new();

    fn store_write(key: Option[Reg], v: Int) -> Unit {
        if (key.is_empty() || reg_arg_list.contains(key.unwrap())) {
            return;
        }

        let ind = key.unwrap();

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

        let ind = key.unwrap();
        last_read[ind] = v;
    }

    for i = 0; i < body.length(); i = i + 1 {
        let asm = body[i];

        // Must clear for jumps
        // (No need to clear for function calls because all registers are preserved)
        match asm {
            J(label) => {
                used_labels = used_labels.add(label);
                last_read.clear();
                last_written.clear();
            }
            Bne(_, _, label) | Bgt(_, _, label) | Beq(_, _, label) => {
                used_labels = used_labels.add(label);
            }
            La(_, label) => {
                // The only kind of label that might jump backwards
                if (label._.ends_with("tailrec")) {
                    last_read.clear();
                    last_written.clear();
                }
                used_labels = used_labels.add(label);
            }
            Call(_) | Jalr(_) => {
                for x in [..reg_arg_list, ..freg_arg_list] {
                    store_read(Some(x), i);
                }
                store_write(Some(A0), i);
                store_write(Some(A1), i);
                store_write(Some(Fa0), i);
            }
            _ => ()
        }

        let used = reg_used(asm);
        store_read(used.rs1, i);
        store_read(used.rs2, i);
        store_write(used.rd, i);
    }

    // Reached the end; store_write() for every register
    // so that registers written once and never read will be eliminated
    for x in [..reg_allocatable_list, ..freg_allocatable_list] {
        store_write(Some(x), body.length());
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

// If a register is never read in the whole function, remove all writes to it
// (Except a0, ..., a7 which are arguments)
pub fn opt_remove_unread(body: Array[RvAsm]) -> Array[RvAsm] {
    let mut read: @immut/hashset.T[Reg] = @immut/hashset.T::new();

    fn store_read(x: Option[Reg]) {
        if (x.is_empty().not()) {
            read = read.add(x.unwrap());
        }
    }

    for i = 0; i < body.length(); i = i + 1 {
        let asm = body[i];

        let used = reg_used(asm);
        store_read(used.rs1);
        store_read(used.rs2);
    }

    let opt = [];
    let arg_list = [..reg_arg_list, ..freg_arg_list];
    for i = 0; i < body.length(); i = i + 1 {
        let used = reg_used(body[i]);

        if (used.rd.is_empty().not()) {
            let rd = used.rd.unwrap();
            if (read.contains(rd).not() && arg_list.contains(rd).not()) {
                continue;
            }
        }

        opt.push(body[i]);
    }

    return opt;
}


fn atoi(arr: String) -> Option[Int] {
    let mut x = 0;
    let mut z = 0;
    while (x < arr.length() && @lex.is_digit(arr[x])) {
        z = z * 10 + arr[x].to_int() - '0'.to_int();
        x += 1;
    }
    if (x == arr.length()) {
        return Some(z);
    }
    return None;
}

// Looks at 2 consecutive instructions and sees if there is a better way to rewrite.
pub fn opt_peephole_2(body: Array[RvAsm]) -> Array[RvAsm] {
    let result = [];
    let mut i = 0;
    while (i < body.length() - 1) {
        match (body[i], body[i + 1]) {
            (Mv(a, b), Mv(c, d)) => {
                // If it is like "a = b; b = a;"
                // then remove the second operation
                if (b == c && a == d) {
                    result.push(body[i]);
                    i += 2;
                    continue;
                }
            }
            (FmvD(a, b), FmvD(c, d)) => {
                // same as mv
                if (b == c && a == d) {
                    result.push(body[i]);
                    i += 2;
                    continue;
                }
            }
            (FmvDX(a, b), FmvD(c, d)) => {
                // If it is like "a = b; c = a";
                // then make the second one "c = b"
                if (a == d) {
                    result.push(body[i]);
                    result.push(FmvDX(c, b));
                    i += 2;
                    continue;
                }
            }
            (Li(a, imm), Mv(b, c)) => {
                // If it is like "a = 0; b = a;"
                // then make the second one "b = 0"
                if (a == c) {
                    result.push(body[i]);
                    result.push(Li(b, imm));
                    i += 2;
                    continue;
                }
            }
            (La(a, label), Mv(b, c)) => {
                // If it is like "a = &func; b = a;"
                // then make the second one "b = &func"
                if (a == c) {
                    result.push(body[i]);
                    result.push(La(b, label));
                    i += 2;
                    continue;
                }
            }
            (Li(a, imm), Add(b, c, d)) => {
                // li a, imm; add b, c, a => addi b, c, imm
                // li a, imm; add b, a, c => addi b, c, imm

                // Note: we sometimes load int64 into a register
                // but it doesn't matter because this combination do not happen
                let v = atoi(imm);

                // Addi supports up to 12 bits of immediate, so no more than 2^11 (sign bit)
                if (a == d && v.is_empty().not() && v.unwrap() < 2048 && v.unwrap() >= -2048) {
                    result.push(body[i]);
                    result.push(Addi(b, c, v.unwrap()));
                    i += 2;
                    continue;
                }

                if (a == c && v.is_empty().not() && v.unwrap() < 2048 && v.unwrap() >= -2048) {
                    result.push(body[i]);
                    result.push(Addi(b, d, v.unwrap()));
                    i += 2;
                    continue;
                }
            }
            (Li(a, imm), Sub(b, c, d)) => {
                // li a, imm; sub b, c, a => addi b, c, -imm
                
                let v = atoi(imm);
                
                if (a == d && v.is_empty().not() && v.unwrap() <= 2048 && v.unwrap() > -2048) {
                    result.push(body[i]);
                    result.push(Addi(b, c, -v.unwrap()));
                    i += 2;
                    continue;
                }
            }
            (Li(a, imm), Slli(b, c, 3)) => {
                // li a, imm; slli a, a, 3 => li a, imm * 8;
                // Seen on array manipulation
                
                let v = atoi(imm);
                
                if (a == b && a == c && v.is_empty().not()) {
                    result.push(Li(a, (8 * v.unwrap()).to_string()));
                    i += 2;
                    continue;
                }
            }
            (Li(a, imm), Bgt(b, c, label)) => {
                // li a, 0; bgt b, a, label => bgt b, zero, label
                
                if (a == c && imm == "0") {
                    result.push(body[i]);
                    result.push(Bgt(b, Zero, label));
                    i += 2;
                    continue;
                }
            }
            (Li(a, imm), Bne(b, c, label)) => {
                // li a, 0; bne b, a, label => bgt b, zero, label
                
                if (a == c && imm == "0") {
                    result.push(body[i]);
                    result.push(Bne(b, Zero, label));
                    i += 2;
                    continue;
                }
            }
            (Add(a, b, c), Mv(d, e)) => {
                // add a, b, c; mv d, a => add d, b, c; mv a, d
                // Perhaps makes more optimization usable
                if (a == e) {
                    result.push(Add(d, b, c));
                    result.push(Mv(a, d));
                    i += 2;
                    continue;
                }
            }
            (Sub(a, b, c), Mv(d, e)) => {
                // same goes for sub
                if (a == e) {
                    result.push(Sub(d, b, c));
                    result.push(Mv(a, d));
                    i += 2;
                    continue;
                }
            }
            (Xori(a, b, 1), Xori(c, d, 1)) => {
                // xori a, a, 1; xori a, a, 1 => nop
                if (a == b && a == c && a == d) {
                    i += 2;
                    continue;
                }
            }
            _ => ()
        }

        result.push(body[i]);
        i += 1;
    }

    // We haven't pushed this in the loop
    if (body.length() > 0) {
        result.push(body[body.length() - 1]);
    }

    return result;
}

// Remove instructions that have no effect.
pub fn opt_remove_identical(body: Array[RvAsm]) -> Array[RvAsm] {
    let mut i = 0;
    let result = [];
    while (i < body.length()) {
        match body[i] {
            Addi(a, b, 0) => {
                // Remove "addi a, a, 0"
                if (a != b) {
                    result.push(body[i]);
                }
            }
            Mv(a, b) => {
                // Remove "mv a, a"
                // Remove "mv zero, b"
                if (a != b && a != Zero) {
                    result.push(body[i]);
                }
            }
            Li(a, _) => {
                // Remove "li zero, b"
                if (a != Zero) {
                    result.push(body[i]);
                }
            }
            FmvD(a, b) => {
                // Remove "fmv.d a, a"
                if (a != b) {
                    result.push(body[i]);
                }
            }
            J(a) => {
                result.push(body[i]);
                if (a._.ends_with("_tailrec")) {
                    i += 1;
                    while (i < body.length()) {
                        match body[i] {
                            Label(_) => break;
                            _ => i += 1;
                        }
                    }
                    continue;
                }
            }
            Nop => ()
            _ => result.push(body[i])
        }
        i += 1;
    }
    return result;
}

// If we know s1 = s2, then we can substitute s2 wherever s1 appears
// The same goes for labels and immediates as well
pub fn opt_inline_var(body: Array[RvAsm]) -> Array[RvAsm] {
    let mut i = 0;
    let result = [];
    let ref: Map[Reg, Reg] = {};
    let label: Map[Reg, String] = {};
    let imms: Map[Reg, String] = {};

    while (i < body.length()) {
        let file = reg_used(body[i]);

        match body[i] {
            Jalr(x) => {
                if (label[x].is_empty().not()) {
                    result.push(Call(label[x].unwrap()));
                } else {
                    result.push(body[i]);
                }
            }
            Mv(x, y) => {
                if (imms.contains(y)) {
                    result.push(Li(x, imms[y].unwrap()));
                } else {
                    result.push(register_rename(body[i], fn (reg) { deref(ref, reg) }, fn (x) {x}));
                }
            }
            _ => result.push(register_rename(body[i], fn (reg) { deref(ref, reg) }, fn (x) {x}));
        }

        if (file.rd.is_empty().not()) {
            let invalid = file.rd.unwrap();
            let copy = Map::from_iter(ref.iter());

            // Can't just remove on ref; otherwise Iter gets invalidated
            for k, v in copy {
                if (k == invalid || v == invalid) {
                    ref.remove(k);
                }
            }
            label.remove(invalid);
            imms.remove(invalid);
        }

        match body[i] {
            Mv(a, b) | FmvD(a, b) => { ref[a] = b; label.remove(a); imms.remove(a); }

            Label(_) | J(_) => { ref.clear(); label.clear(); imms.clear(); }

            Call(_) | Jalr(_) => {
                let copy = Map::from_iter(ref.iter());
                for k, v in copy {
                    if (arg_list.contains(k) || arg_list.contains(v)) {
                        ref.remove(k);
                    }
                }
                for x in arg_list {
                    label.remove(x);
                    imms.remove(x);
                }
            }

            La(a, x) => label[a] = x._;
            Li(a, x) => imms[a] = x;
            
            _ => ();
        }

        i += 1;
    }
    return result;
}

fn identify_loop(body: Array[RvAsm]) -> Option[(Int, Int)] {
        // Begin of a loop (at the label)
    let mut begin = 0;
    while (begin < body.length()) {
        match body[begin] {
            Label(a) => if (a.ends_with("_tailrec")) {
                break;
            }
            _ => ();
        }
        begin += 1;
    }

    if (begin == body.length()) {
        return None;
    }

    // End of a loop (at the j instruction)
    let mut end = begin + 1;
    while (end < body.length()) {
        match body[end] {
            J(a) => if (a._.ends_with("_tailrec")) {
                break;
            }
            _ => ();
        }
        end += 1;
    }

    // There's simply no loop in the function
    if (end == body.length()) {
        return None;
    }

    return Some((begin, end));
}


// If something is irrelevant with the loop variable
// then put these things outside the loop

// Note: this function expects unconsolidated assembly
// (more like a 3-address IR)
pub fn opt_loop_invariant(body: Array[RvAsm], fun: @closure.FuncDef) -> Array[RvAsm] {
    let range = identify_loop(body);
    if (range == None) {
        return body;
    }

    let (begin, end) = range.unwrap();

    // Verify only one path does tail call;
    // Don't handle things like
    // f() { if (a) { 1 } else { if (..) { f() } else { f() } } }
    // because it's really complicated

    let mut i = end + 1;
    while (i < body.length()) {
        match body[i] {
            J(a) => if (a._.ends_with("_tailrec")) {
                return body;
            }
            _ => ()
        }
        i += 1;
    }

    // Now verify the invariants
    // At this stage, everything is immutable
    // So checking rs1 and rs2 should be enough

    i = begin + 1;

    let involved = [];
    let uninvolved = [];
    let reg_preserve = [];
    let inv_regs: @immut/hashset.T[Reg] =
        @immut/hashset.T::from_array(fun.args.map(fn (x) { Fake(x) }) + reg_arg_list);

    let values: Map[String, Reg] = { "0": Zero };
    let map: Map[Reg, Reg] = {};

    fn rrename(r) {
        match map[r] {
            Some(t) => t
            None => r
        }
    }

    while (i < end) {
        match body[i] {
            // In opt_realloc we test for these
            // so when you add something here, must update another
            La(a, Label(x)) | Li(a, x) => {
                fn rename(r) {
                    match values[x] {
                        Some(t) => { map[r] = t; t }
                        None => r
                    }
                }
                if (inv_regs.contains(a).not()) {
                    if (values.contains(x).not()) {
                        values[x] = a;
                    }

                    uninvolved.push(register_rename(body[i], rename, rename));
                } else {
                    involved.push(register_rename(body[i], rename, rename));
                }
            }
            _ => involved.push(register_rename(body[i], rrename, rrename));
        }
        i += 1;
    }

    for x in uninvolved {
        let used = reg_used(x);
        if (used.rd.is_empty().not()) {
            reg_preserve.push(Mv(used.rd.unwrap(), used.rd.unwrap()));
        }
        if (used.rs1.is_empty().not()) {
            reg_preserve.push(Mv(used.rs1.unwrap(), used.rs1.unwrap()));
        }
        if (used.rs2.is_empty().not()) {
            reg_preserve.push(Mv(used.rs2.unwrap(), used.rs2.unwrap()));
        }
    }


    let result = Array::from_iter(body[:begin].iter()) +
        uninvolved + [Label("\{fun.old_name}_tailrec")] + involved + reg_preserve +
            Array::from_iter(body[end:].iter());

    return result;
}

/// This function inlines loop invariants
pub fn opt_inline_loopvar(body: Array[RvAsm]) -> Array[RvAsm] {
    let range = identify_loop(body);
    let mut new_body = body;
    if (range.is_empty()) {
        return body;
    }

    let (begin, end) = range.unwrap();
    let invar: Map[Reg, String] = {};

    for x in body[:begin] {
        // These are the exact things we extract for loop invariants
        // if you change that function, must also change here
        match x {
            La(a, Label(x)) | Li(a, x)=> {
                invar[a] = x;
            }
            _ => ()
        }
    }

    let middle = [];
    for x in body[begin: end] {
        match x {
            Add(a, b, c) => {
                if (invar.contains(c)) {
                    let v = atoi(invar[c].unwrap());
                    if (v.is_empty().not()) {
                        let w = v.unwrap();
                        if (w < 2048 && w >= -2048) {
                            middle.push(Addi(a, b, w));
                            continue;
                        }
                    }
                }
                if (invar.contains(b)) {
                    let v = atoi(invar[b].unwrap());
                    if (v.is_empty().not()) {
                        let w = v.unwrap();
                        if (w < 2048 && w >= -2048) {
                            middle.push(Addi(a, c, w));
                            continue;
                        }
                    }
                }
            }
            Sub(a, b, c) => {
                if (invar.contains(c)) {
                    let v = atoi(invar[c].unwrap());
                    if (v.is_empty().not()) {
                        let w = v.unwrap();
                        if (w <= 2048 && w > -2048) {
                            middle.push(Addi(a, b, -w));
                            continue;
                        }
                    }
                }
            }
            Jalr(a) => {
                if (invar.contains(a)) {
                    middle.push(J(invar[a].unwrap()));
                    continue;
                }
            }
            _ => ()
        }
        middle.push(x);
    }
    
    new_body = [..body[:begin], ..middle, ..body[end: ]];

    return new_body;
}

/// This function redoes register allocation
/// (Map existing allocation to another one)
/// in case we used less register after optimization
pub fn opt_realloc(body: Array[RvAsm]) -> Array[RvAsm] {
    t.offset = 0;

    let rename: Map[Reg, Reg] = {};

    let mut has_call = false;
    for x in body {
        match x {
            Call(_) | Jalr(_) => has_call = true;
            _ => ()
        }
    }

    let list = if (has_call) {
        reg_allocatable_list
    } else {
        reg_allocatable_list_biased
    };
    let listf = if (has_call) {
        freg_allocatable_list
    } else {
        freg_allocatable_list_biased
    };

    let mut next = 0;
    let mut nextf = 0;
    let no_rename = arg_list + [Ra, Sp, Fp, Tp, Gp, Zero, S11, S10, T6, Ft8, Ft9, Ft10];

    fn record(r) {
        match r {
            Some(reg) => {
                if (no_rename.contains(reg).not() && rename.contains(reg).not()) {
                    if (is_freg(reg)) {
                        if (nextf < listf.length()) {
                            rename[reg] = listf[nextf];
                            nextf += 1;
                        } else {
                            rename[reg] = SpiltDouble(t.offset);
                            t.offset += 8;
                        }
                    } else {
                        if (next < list.length()) {
                            rename[reg] = list[next];
                            next += 1;
                        } else {
                            rename[reg] = Spilt(t.offset);
                            t.offset += 8;
                        }
                    }
                }
            }
            None => ()
        }
    }

    for x in body {
        let used = reg_used(x);
        record(used.rd);
        record(used.rs1);
        record(used.rs2);
    }

    fn realloc(r) {
        match rename[r] {
            Some(reg) => reg
            None => r
        }
    }

    return body.map(fn (x) { register_rename(x, realloc, realloc) });
}


/// Make all fake registers real
pub fn consolidate(body: Array[RvAsm]) -> Array[RvAsm] {
    return body.map(fn (asm) {
        register_rename(asm, defake, defake);
    });
}