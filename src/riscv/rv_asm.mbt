pub enum RvAsm {
    // reg-reg arith
    Add(Reg, Reg, Reg)
    Sub(Reg, Reg, Reg)
    Xor(Reg, Reg, Reg)
    Or(Reg, Reg, Reg)
    And(Reg, Reg, Reg)
    Sll(Reg, Reg, Reg)
    Srl(Reg, Reg, Reg)
    Sra(Reg, Reg, Reg)
    Slt(Reg, Reg, Reg)
    Sltu(Reg, Reg, Reg)
    // reg-imm arith
    Addi(Reg, Reg, Int)
    Xori(Reg, Reg, Int)
    Ori(Reg, Reg, Int)
    Andi(Reg, Reg, Int)
    Slli(Reg, Reg, Int)
    Srli(Reg, Reg, Int)
    Srai(Reg, Reg, Int)
    Slti(Reg, Reg, Int)
    Sltiu(Reg, Reg, Int)
    // mem
    // memory access
    Lb(Reg, MemAccess[Reg, Int])
    Lh(Reg, MemAccess[Reg, Int])
    Lw(Reg, MemAccess[Reg, Int])
    Ld(Reg, MemAccess[Reg, Int])
    Lbu(Reg, MemAccess[Reg, Int])
    Lhu(Reg, MemAccess[Reg, Int])
    Lwu(Reg, MemAccess[Reg, Int])
    Sb(Reg, MemAccess[Reg, Int])
    Sh(Reg, MemAccess[Reg, Int])
    Sw(Reg, MemAccess[Reg, Int])
    Sd(Reg, MemAccess[Reg, Int])
    // control flow
    Beq(Reg, Reg, Label)
    Bne(Reg, Reg, Label)
    Blt(Reg, Reg, Label)
    Bge(Reg, Reg, Label)
    Ble(Reg, Reg, Label)
    Bgt(Reg, Reg, Label)
    Bltu(Reg, Reg, Label)
    Bgeu(Reg, Reg, Label)
    // system
    Ecall
    // rv32/64m
    Mul(Reg, Reg, Reg)
    Mulw(Reg, Reg, Reg)
    Mulh(Reg, Reg, Reg)
    Mulhsu(Reg, Reg, Reg)
    Mulhu(Reg, Reg, Reg)
    Div(Reg, Reg, Reg)
    Divw(Reg, Reg, Reg)
    Divu(Reg, Reg, Reg)
    Rem(Reg, Reg, Reg)
    Remw(Reg, Reg, Reg)
    Remu(Reg, Reg, Reg)
    // rvf
    FaddD(Reg, Reg, Reg)
    FsubD(Reg, Reg, Reg)
    FmulD(Reg, Reg, Reg)
    FdivD(Reg, Reg, Reg)
    Fld(Reg, MemAccess[Reg, Int])
    Fsd(Reg, MemAccess[Reg, Int])
    FeqD(Reg, Reg, Reg)
    FleD(Reg, Reg, Reg)
    FmvDX(Reg, Reg)
    FmvXD(Reg, Reg)
    // pseudo instructions
    Nop
    La(Reg, Label)
    Li(Reg, String)
    Neg(Reg, Reg)
    FnegD(Reg, Reg)
    Mv(Reg, Reg)
    FmvD(Reg, Reg)
    J(Label)
    Jalr(Reg)
    Jr(Reg)
    Call(Label)
    Tail(Label)
    Ret
    // Comments
    Label(String)
    Comment(String)
}

pub fn RvAsm::to_string(self: RvAsm) -> String {
    let l = Buffer::new();
    Show::output(self, l);
    l.to_string();
}

struct Where {
    mut x: Int

    mut fx: Int
}

let where: Where = { x: 0, fx: 0 };

fn which() -> Reg {
    match where.x {
        0 => S10
        1 => S11
        x => @util.die("emit: bad which(): \{x}")
    }
}

fn whichf() -> Reg {
    match where.fx {
        0 => Fs10
        1 => Fs11
        x => @util.die("emit: bad whichf(): \{x}")
    }
}

fn offset(r: Reg) -> Int {
    match r {
        Spilt(x) => x
        SpiltDouble(x) => x
        _ => -1
    }
}

fn spill(logger: Logger, r: Reg) -> Reg {
    let x = offset(r);
    if (x != -1) {
        if (is_freg(r)) {
            let t = whichf();
            where.fx += 1;
            write2mem(logger, "fld", t, { base: Sp, offset: x });
            logger.write_string("\n    ");
            t
        } else {
            let t = which();
            where.x += 1;
            write2mem(logger, "ld", t, { base: Sp, offset: x });
            logger.write_string("\n    ");
            t
        }
    } else {
        r
    }
}

fn unspill(logger: Logger, r: Reg) -> Unit {
    let x = offset(r);
    if (x != -1) {
        if (is_freg(r)) {
            logger.write_string("\n    ");
            write2mem(logger, "fsd", Fs10, { base: Sp, offset: x });
            logger.write_string("\n    ");
        } else {
            logger.write_string("\n    ");
            write2mem(logger, "sd", S10, { base: Sp, offset: x });
            logger.write_string("\n    ");
        }
    }
}

fn despill(r: Reg) -> Unit {
    let x = offset(r);
    if (x != -1) {
        if (is_freg(r)) {
            where.fx -= 1;
        } else {
            where.x -= 1;
        }
    }
}

fn spill_write(r: Reg) -> Reg {
    let x = offset(r);
    if (x != -1) {
        if (is_freg(r)) {
            Fs10
        } else {
            S10
        }
    } else {
        r
    }
}

fn write3(
    logger : Logger,
    op : String,
    rd : Reg,
    rs1 : Reg,
    rs2 : Reg
) -> Unit {
    let t1 = spill_write(rd);
    let t2 = spill(logger, rs1);
    let t3 = spill(logger, rs2);
    logger.write_string(op)
    logger.write_string(" ")
    Show::output(t1, logger)
    logger.write_string(", ")
    Show::output(t2, logger)
    logger.write_string(", ")
    Show::output(t3, logger)
    despill(rs2);
    despill(rs1);
    unspill(logger, rd);
}

fn write2imm(
    logger : Logger,
    op : String,
    rd : Reg,
    rs1 : Reg,
    imm : Int
) -> Unit {
    let t1 = spill_write(rd);
    let t2 = spill(logger, rs1);
    logger.write_string(op)
    logger.write_string(" ")
    Show::output(t1, logger)
    logger.write_string(", ")
    Show::output(t2, logger)
    logger.write_string(", ")
    logger.write_string(imm.to_string())
    despill(rs1);
    unspill(logger, rd);
}

fn write2label(
    logger : Logger,
    op : String,
    rs1 : Reg,
    rs2 : Reg,
    label : Label
) -> Unit {
    let t1 = spill(logger, rs1);
    let t2 = spill(logger, rs2);
    logger.write_string(op)
    logger.write_string(" ")
    Show::output(t1, logger)
    logger.write_string(", ")
    Show::output(t2, logger)
    logger.write_string(", ")
    logger.write_string(label._)
    despill(rs2);
    despill(rs1);
}

fn write2mem(
    logger : Logger,
    op : String,
    rd : Reg,
    mem : MemAccess[Reg, Int]
) -> Unit {
    
    let t1 = spill_write(rd);
    let t2 = spill(logger, mem.base);
    logger.write_string(op)
    logger.write_string(" ")
    Show::output(t1, logger)
    logger.write_string(", ")
    logger.write_string(mem.offset.to_string())
    logger.write_string("(")
    Show::output(t2, logger)
    logger.write_string(")")
    unspill(logger, rd);
    despill(mem.base);
}

fn write2(
    logger : Logger,
    op : String,
    rd : Reg,
    rs1 : Reg
) -> Unit {
    let t1 = spill_write(rd);
    let t2 = spill(logger, rs1);
    logger.write_string(op)
    logger.write_string(" ")
    Show::output(t1, logger)
    logger.write_string(", ")
    Show::output(t2, logger)
    despill(rs1);
    unspill(logger, rd);
}

impl Show for RvAsm with output(self, logger) {
    match self {
        Label(_) => ()
        _ => logger.write_string("    ")
    }
    match self {
        Add(rd, rs1, rs2) => write3(logger, "add", rd, rs1, rs2)
        Sub(rd, rs1, rs2) => write3(logger, "sub", rd, rs1, rs2)
        Xor(rd, rs1, rs2) => write3(logger, "xor", rd, rs1, rs2)
        Or(rd, rs1, rs2) => write3(logger, "or", rd, rs1, rs2)
        And(rd, rs1, rs2) => write3(logger, "and", rd, rs1, rs2)
        Sll(rd, rs1, rs2) => write3(logger, "sll", rd, rs1, rs2)
        Srl(rd, rs1, rs2) => write3(logger, "srl", rd, rs1, rs2)
        Sra(rd, rs1, rs2) => write3(logger, "sra", rd, rs1, rs2)
        Slt(rd, rs1, rs2) => write3(logger, "slt", rd, rs1, rs2)
        Sltu(rd, rs1, rs2) => write3(logger, "sltu", rd, rs1, rs2)
        Addi(rd, rs1, imm) => write2imm(logger, "addi", rd, rs1, imm)
        Xori(rd, rs1, imm) => write2imm(logger, "xori", rd, rs1, imm)
        Ori(rd, rs1, imm) => write2imm(logger, "ori", rd, rs1, imm)
        Andi(rd, rs1, imm) => write2imm(logger, "andi", rd, rs1, imm)
        Slli(rd, rs1, imm) => write2imm(logger, "slli", rd, rs1, imm)
        Srli(rd, rs1, imm) => write2imm(logger, "srli", rd, rs1, imm)
        Srai(rd, rs1, imm) => write2imm(logger, "srai", rd, rs1, imm)
        Slti(rd, rs1, imm) => write2imm(logger, "slti", rd, rs1, imm)
        Sltiu(rd, rs1, imm) => write2imm(logger, "sltiu", rd, rs1, imm)
        Lb(rd, mem) => write2mem(logger, "lb", rd, mem)
        Lh(rd, mem) => write2mem(logger, "lh", rd, mem)
        Lw(rd, mem) => write2mem(logger, "lw", rd, mem)
        Ld(rd, mem) => write2mem(logger, "ld", rd, mem)
        Lbu(rd, mem) => write2mem(logger, "lbu", rd, mem)
        Lhu(rd, mem) => write2mem(logger, "lhu", rd, mem)
        Lwu(rd, mem) => write2mem(logger, "lwu", rd, mem)
        Sb(rd, mem) => write2mem(logger, "sb", rd, mem)
        Sh(rd, mem) => write2mem(logger, "sh", rd, mem)
        Sw(rd, mem) => write2mem(logger, "sw", rd, mem)
        Sd(rd, mem) => write2mem(logger, "sd", rd, mem)
        Beq(rs1, rs2, label) => write2label(logger, "beq", rs1, rs2, label)
        Bne(rs1, rs2, label) => write2label(logger, "bne", rs1, rs2, label)
        Blt(rs1, rs2, label) => write2label(logger, "blt", rs1, rs2, label)
        Bge(rs1, rs2, label) => write2label(logger, "bge", rs1, rs2, label)
        Ble(rs1, rs2, label) => write2label(logger, "ble", rs1, rs2, label)
        Bgt(rs1, rs2, label) => write2label(logger, "bgt", rs1, rs2, label)
        Bltu(rs1, rs2, label) => write2label(logger, "bltu", rs1, rs2, label)
        Bgeu(rs1, rs2, label) => write2label(logger, "bgeu", rs1, rs2, label)
        Ecall => logger.write_string("ecall")
        Mul(rd, rs1, rs2) => write3(logger, "mul", rd, rs1, rs2)
        Mulw(rd, rs1, rs2) => write3(logger, "mulw", rd, rs1, rs2)
        Mulh(rd, rs1, rs2) => write3(logger, "mulh", rd, rs1, rs2)
        Mulhsu(rd, rs1, rs2) => write3(logger, "mulhsu", rd, rs1, rs2)
        Mulhu(rd, rs1, rs2) => write3(logger, "mulhu", rd, rs1, rs2)
        Div(rd, rs1, rs2) => write3(logger, "div", rd, rs1, rs2)
        Divw(rd, rs1, rs2) => write3(logger, "divw", rd, rs1, rs2)
        Divu(rd, rs1, rs2) => write3(logger, "divu", rd, rs1, rs2)
        Rem(rd, rs1, rs2) => write3(logger, "rem", rd, rs1, rs2)
        Remw(rd, rs1, rs2) => write3(logger, "remw", rd, rs1, rs2)
        Remu(rd, rs1, rs2) => write3(logger, "remu", rd, rs1, rs2)
        FaddD(rd, rs1, rs2) => write3(logger, "fadd.d", rd, rs1, rs2)
        FsubD(rd, rs1, rs2) => write3(logger, "fsub.d", rd, rs1, rs2)
        FmulD(rd, rs1, rs2) => write3(logger, "fmul.d", rd, rs1, rs2)
        FdivD(rd, rs1, rs2) => write3(logger, "fdiv.d", rd, rs1, rs2)
        Fld(rd, mem) => write2mem(logger, "fld", rd, mem)
        Fsd(rd, mem) => write2mem(logger, "fsd", rd, mem)
        FeqD(rd, rs1, rs2) => write3(logger, "feq.d", rd, rs1, rs2)
        FleD(rd, rs1, rs2) => write3(logger, "fle.d", rd, rs1, rs2)
        FmvDX(rd, rs1) => write2(logger, "fmv.d.x", rd, rs1)
        FmvXD(rd, rs1) => write2(logger, "fmv.x.d", rd, rs1)
        Nop => logger.write_string("nop")
        La(rd, label) => {
            let t1 = spill_write(rd);
            logger.write_string("la ")
            Show::output(t1, logger)
            logger.write_string(", ")
            logger.write_string(label._)
            unspill(logger, rd);
        }
        Li(rd, imm) => {
            let t1 = spill_write(rd);
            logger.write_string("li ")
            Show::output(t1, logger)
            logger.write_string(", ")
            logger.write_string(imm)
            unspill(logger, rd);
        }
        Neg(rd, rs1) => write2(logger, "neg", rd, rs1)
        FnegD(rd, rs1) => write2(logger, "fneg.d", rd, rs1)
        Mv(rd, rs1) => write2(logger, "mv", rd, rs1)
        FmvD(rd, rs1) => write2(logger, "fmv.d", rd, rs1)
        J(label) => {
            logger.write_string("j ")
            logger.write_string(label._)
        }
        Jalr(rs1) => {
            let t1 = spill(logger, rs1);
            logger.write_string("jalr ")
            Show::output(t1, logger)
            despill(rs1);
        }
        Jr(rs1) => {
            let t1 = spill(logger, rs1);
            logger.write_string("jr ")
            Show::output(t1, logger)
            despill(rs1);
        }
        Call(label) => {
            logger.write_string("call ")
            logger.write_string(label._)
        }
        Tail(label) => {
            logger.write_string("tail ")
            logger.write_string(label._)
        }
        Ret => logger.write_string("ret")
        Label(label) => {
            logger.write_string(label)
            logger.write_string(":")
        }
        Comment(comment) => {
            logger.write_string("# ")
            logger.write_string(comment)
        }
    }
}
