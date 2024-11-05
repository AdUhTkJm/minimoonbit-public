fn defake(reg: Reg) -> Reg {
    match reg {
        Fake(name) => match t.regs[name] {
            Some(w) => w
            None => @util.die("emit: regalloc failed: \{reg}")
        }
        Arg(i) => reg_arg_list[i]
        z => z
    }
}

// Removes useless instructions
// If a register is written twice without any read in between, the first write can be ignored
pub fn opt_remove_useless(body: Array[RvAsm]) -> Array[RvAsm] {
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
            J(label) | Bne(_, _, label) | Bgt(_, _, label) | Beq(_, _, label) => {
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
            (Xori(a, b, 1), Xori(c, d, 1)) => {
                // xori a, a, 1; xori a, a, 1 => ()
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
    result.push(body[body.length() - 1]);

    return result;
}

pub fn opt_remove_identical(body: Array[RvAsm]) -> Array[RvAsm] {
    let mut i = 0;
    let result = [];
    while (i < body.length()) {
        match body[i] {
            Addi(a, b, 0) => {
                // Remove "addi a, a, 0"
                if (weak_eq(a, b).not()) {
                    result.push(body[i]);
                }
            }
            Mv(a, b) => {
                // Remove "mv a, a"
                if (weak_eq(a, b).not()) {
                    result.push(body[i]);
                }
            }
            _ => result.push(body[i])
        }
        i += 1;
    }
    return result;
}

// If we know s1 = s2, then we can substitute s2 wherever s1 appears
pub fn opt_inline_var(body: Array[RvAsm]) -> Array[RvAsm] {
    let mut i = 0;
    let result = [];
    let ref: Map[Reg, Reg] = {};

    while (i < body.length()) {
        let file = reg_used(body[i]);

        result.push(register_rename(body[i], fn (reg) {
            match ref[reg] {
                Some(t) => t
                None => reg
            }
        }, fn (x) {x}));

        if (file.rd.is_empty().not()) {
            let invalid = file.rd.unwrap();
            let copy = Map::from_iter(ref.iter());

            // Can't just remove on ref; otherwise Iter gets invalidated
            for k, v in copy {
                if (k == invalid || v == invalid) {
                    ref.remove(k);
                }
            }
        }

        match body[i] {
            Mv(a, b) => ref[a] = b;

            Label(_) | J(_) | Bne(_) | Beq(_) |
            Bge(_) | Bgeu(_) | Bgt(_) | Ble(_) | Blt(_) |
            Bltu(_) => ref.clear();

            Call(_) | Jalr(_) => {
                let copy = Map::from_iter(ref.iter());
                for k, v in copy {
                    if (k == A0 || v == A0 || k == A1 || v == A1) {
                        ref.remove(k);
                    }
                }
            }

            _ => ();
        }

        i += 1;
    }
    return result;
}

pub fn consolidate(body: Array[RvAsm]) -> Array[RvAsm] {
    return body.map(fn (asm) { register_rename(asm, defake, defake); });
}