// Removes useless instructions
// If a register is written twice without any read in between, the first write can be ignored
pub fn opt_remove_useless(body: Array[RvAsm]) -> Array[RvAsm] {
    fn defake(reg: Reg) -> Reg {
        match reg {
            Fake(name) => match t.regs[name] {
                Some(w) => w
                None => Spilt(0) //@util.die("emit: regalloc failed: \{reg}")
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
            println("Delete: \{body[i]}")
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