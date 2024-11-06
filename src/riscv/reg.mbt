struct MemAccess[TBase, TOff] {
    base : TBase
    offset : TOff
} derive(Show)

type Label String derive(Show, Eq, Hash)

/// RISC-V register
pub enum Reg {
    Zero
    Ra
    Sp
    Gp
    Tp
    T0
    T1
    T2
    Fp
    S1
    A0
    A1
    A2
    A3
    A4
    A5
    A6
    A7
    S2
    S3
    S4
    S5
    S6
    S7
    S8
    S9
    S10
    S11
    T3
    T4
    T5
    T6
    Ft0
    Ft1
    Ft2
    Ft3
    Ft4
    Ft5
    Ft6
    Ft7
    Fs0
    Fs1
    Fa0
    Fa1
    Fa2
    Fa3
    Fa4
    Fa5
    Fa6
    Fa7
    Fs2
    Fs3
    Fs4
    Fs5
    Fs6
    Fs7
    Fs8
    Fs9
    Fs10
    Fs11
    Ft8
    Ft9
    Ft10
    Ft11
    Fake(@types.Name)
    Arg(Int)
    Spilt(Int)
} derive(Eq, Compare, Hash)

pub let reg_temp_list : Array[Reg] = [T0, T1, T2, T3, T4, T5]

pub let reg_saved_list : Array[Reg] = [
    // S0, <- fp
    S1,
    S2,
    S3,
    S4,
    S5,
    S6,
    S7,
    S8,
    S9,
]

pub let reg_arg_list: Array[Reg] = [A0, A1, A2, A3, A4, A5, A6, A7]

pub let reg_caller_saved_list: Array[Reg] = reg_temp_list + reg_arg_list

pub let reg_callee_saved_list: Array[Reg] = reg_saved_list

pub let reg_allocatable_list: Array[Reg] = reg_saved_list + reg_temp_list

pub let reg_allocatable_list_biased: Array[Reg] = reg_temp_list + reg_saved_list
pub fn Reg::to_string(self : Reg) -> String {
    match self {
        Zero => "zero"
        Ra => "ra"
        Sp => "sp"
        Gp => "gp"
        Tp => "tp"
        T0 => "t0"
        T1 => "t1"
        T2 => "t2"
        Fp => "s0"
        S1 => "s1"
        A0 => "a0"
        A1 => "a1"
        A2 => "a2"
        A3 => "a3"
        A4 => "a4"
        A5 => "a5"
        A6 => "a6"
        A7 => "a7"
        S2 => "s2"
        S3 => "s3"
        S4 => "s4"
        S5 => "s5"
        S6 => "s6"
        S7 => "s7"
        S8 => "s8"
        S9 => "s9"
        S10 => "s10"
        S11 => "s11"
        T3 => "t3"
        T4 => "t4"
        T5 => "t5"
        T6 => "t6"
        Ft0 => "ft0"
        Ft1 => "ft1"
        Ft2 => "ft2"
        Ft3 => "ft3"
        Ft4 => "ft4"
        Ft5 => "ft5"
        Ft6 => "ft6"
        Ft7 => "ft7"
        Fs0 => "fs0"
        Fs1 => "fs1"
        Fa0 => "fa0"
        Fa1 => "fa1"
        Fa2 => "fa2"
        Fa3 => "fa3"
        Fa4 => "fa4"
        Fa5 => "fa5"
        Fa6 => "fa6"
        Fa7 => "fa7"
        Fs2 => "fs2"
        Fs3 => "fs3"
        Fs4 => "fs4"
        Fs5 => "fs5"
        Fs6 => "fs6"
        Fs7 => "fs7"
        Fs8 => "fs8"
        Fs9 => "fs9"
        Fs10 => "fs10"
        Fs11 => "fs11"
        Ft8 => "ft8"
        Ft9 => "ft9"
        Ft10 => "ft10"
        Ft11 => "ft11"
        Fake(name) => name.to_string()
        Arg(i) => "arg.\{i}"
        Spilt(i) => "spilt.\{i}"
    }
}

impl Show for Reg with output(self, logger : Logger) {
    logger.write_string(self.to_string())
}

pub let freg_temp_list : Array[Reg] = [
    Ft0,
    Ft1,
    Ft2,
    Ft3,
    Ft4,
    Ft5,
    Ft6,
    Ft7,
    Ft8,
    Ft9,
    Ft10,
]

pub let freg_saved_list : Array[Reg] = [
    Fs0,
    Fs1,
    Fs2,
    Fs3,
    Fs4,
    Fs5,
    Fs6,
    Fs7,
    Fs8,
    Fs9,
    Fs10,
    Fs11,
]

pub let freg_arg_list : Array[Reg] = [Fa0, Fa1, Fa2, Fa3, Fa4, Fa5, Fa6, Fa7]

pub let freg_caller_saved_list : Array[Reg] = freg_temp_list + freg_arg_list

pub let freg_callee_saved_list : Array[Reg] = freg_saved_list

pub let freg_allocatable_list : Array[Reg] = freg_callee_saved_list +
    freg_caller_saved_list

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


fn register_rename(asm: RvAsm, rs_fn: (Reg) -> Reg, rd_fn: (Reg) -> Reg) -> RvAsm {
    match asm {
        Add(rd, rs1, rs2) => Add(rd_fn(rd), rs_fn(rs1), rs_fn(rs2));
        Sub(rd, rs1, rs2) => Sub(rd_fn(rd), rs_fn(rs1), rs_fn(rs2));
        Xor(rd, rs1, rs2) => Xor(rd_fn(rd), rs_fn(rs1), rs_fn(rs2));
        Or(rd, rs1, rs2) => Or(rd_fn(rd), rs_fn(rs1), rs_fn(rs2))
        And(rd, rs1, rs2) => And(rd_fn(rd), rs_fn(rs1), rs_fn(rs2))
        Sll(rd, rs1, rs2) => Sll(rd_fn(rd), rs_fn(rs1), rs_fn(rs2))
        Srl(rd, rs1, rs2) => Srl(rd_fn(rd), rs_fn(rs1), rs_fn(rs2))
        Sra(rd, rs1, rs2) => Sra(rd_fn(rd), rs_fn(rs1), rs_fn(rs2))
        Slt(rd, rs1, rs2) => Slt(rd_fn(rd), rs_fn(rs1), rs_fn(rs2))
        Sltu(rd, rs1, rs2) => Sltu(rd_fn(rd), rs_fn(rs1), rs_fn(rs2))
        Addi(rd, rs1, imm) => Addi(rd_fn(rd), rs_fn(rs1), imm)
        Xori(rd, rs1, imm) => Xori(rd_fn(rd), rs_fn(rs1), imm)
        Ori(rd, rs1, imm) => Ori(rd_fn(rd), rs_fn(rs1), imm)
        Andi(rd, rs1, imm) => Andi(rd_fn(rd), rs_fn(rs1), imm)
        Slli(rd, rs1, imm) => Slli(rd_fn(rd), rs_fn(rs1), imm)
        Srli(rd, rs1, imm) => Srli(rd_fn(rd), rs_fn(rs1), imm)
        Srai(rd, rs1, imm) => Srai(rd_fn(rd), rs_fn(rs1), imm)
        Slti(rd, rs1, imm) => Slti(rd_fn(rd), rs_fn(rs1), imm)
        Sltiu(rd, rs1, imm) => Sltiu(rd_fn(rd), rs_fn(rs1), imm)
        Lb(rd, { base: rs1, offset: offset }) => Lb(rd_fn(rd), { base: rs_fn(rs1), offset: offset })
        Lh(rd, { base: rs1, offset: offset }) => Lh(rd_fn(rd), { base: rs_fn(rs1), offset: offset })
        Lw(rd, { base: rs1, offset: offset }) => Lw(rd_fn(rd), { base: rs_fn(rs1), offset: offset })
        Ld(rd, { base: rs1, offset: offset }) => Ld(rd_fn(rd), { base: rs_fn(rs1), offset: offset })
        Lbu(rd, { base: rs1, offset: offset }) => Lbu(rd_fn(rd), { base: rs_fn(rs1), offset: offset })
        Lhu(rd, { base: rs1, offset: offset }) => Lhu(rd_fn(rd), { base: rs_fn(rs1), offset: offset })
        Lwu(rd, { base: rs1, offset: offset }) => Lwu(rd_fn(rd), { base: rs_fn(rs1), offset: offset })
        Sb(rd, { base: rs1, offset: offset }) => Sb(rd_fn(rd), { base: rs_fn(rs1), offset: offset })
        Sh(rd, { base: rs1, offset: offset }) => Sh(rd_fn(rd), { base: rs_fn(rs1), offset: offset })
        Sw(rd, { base: rs1, offset: offset }) => Sw(rd_fn(rd), { base: rs_fn(rs1), offset: offset })
        Sd(rd, { base: rs1, offset: offset }) => Sd(rd_fn(rd), { base: rs_fn(rs1), offset: offset })
        Beq(rs1, rs2, label) => Beq(rs_fn(rs1), rs_fn(rs2), label)
        Bne(rs1, rs2, label) => Bne(rs_fn(rs1), rs_fn(rs2), label)
        Blt(rs1, rs2, label) => Blt(rs_fn(rs1), rs_fn(rs2), label)
        Bge(rs1, rs2, label) => Bge(rs_fn(rs1), rs_fn(rs2), label)
        Ble(rs1, rs2, label) => Ble(rs_fn(rs1), rs_fn(rs2), label)
        Bgt(rs1, rs2, label) => Bgt(rs_fn(rs1), rs_fn(rs2), label)
        Bltu(rs1, rs2, label) => Bltu(rs_fn(rs1), rs_fn(rs2), label)
        Bgeu(rs1, rs2, label) => Bgeu(rs_fn(rs1), rs_fn(rs2), label)
        Mul(rd, rs1, rs2) => Mul(rd_fn(rd), rs_fn(rs1), rs_fn(rs2))
        Mulw(rd, rs1, rs2) => Mulw(rd_fn(rd), rs_fn(rs1), rs_fn(rs2))
        Mulh(rd, rs1, rs2) => Mulh(rd_fn(rd), rs_fn(rs1), rs_fn(rs2))
        Mulhsu(rd, rs1, rs2) => Mulhsu(rd_fn(rd), rs_fn(rs1), rs_fn(rs2))
        Mulhu(rd, rs1, rs2) => Mulhu(rd_fn(rd), rs_fn(rs1), rs_fn(rs2))
        Div(rd, rs1, rs2) => Div(rd_fn(rd), rs_fn(rs1), rs_fn(rs2))
        Divw(rd, rs1, rs2) => Divw(rd_fn(rd), rs_fn(rs1), rs_fn(rs2))
        Divu(rd, rs1, rs2) => Divu(rd_fn(rd), rs_fn(rs1), rs_fn(rs2))
        Rem(rd, rs1, rs2) => Rem(rd_fn(rd), rs_fn(rs1), rs_fn(rs2))
        Remw(rd, rs1, rs2) => Remw(rd_fn(rd), rs_fn(rs1), rs_fn(rs2))
        Remu(rd, rs1, rs2) => Remu(rd_fn(rd), rs_fn(rs1), rs_fn(rs2))
        FaddD(rd, rs1, rs2) => FaddD(rd_fn(rd), rs_fn(rs1), rs_fn(rs2))
        FsubD(rd, rs1, rs2) => FsubD(rd_fn(rd), rs_fn(rs1), rs_fn(rs2))
        FmulD(rd, rs1, rs2) => FmulD(rd_fn(rd), rs_fn(rs1), rs_fn(rs2))
        FdivD(rd, rs1, rs2) => FdivD(rd_fn(rd), rs_fn(rs1), rs_fn(rs2))
        Fld(rd, { base: rs1, offset: offset }) => Fld(rd_fn(rd), { base: rs_fn(rs1), offset: offset })
        Fsd(rd, { base: rs1, offset: offset }) => Fsd(rd_fn(rd), { base: rs_fn(rs1), offset: offset })
        FeqD(rd, rs1, rs2) => FeqD(rd_fn(rd), rs_fn(rs1), rs_fn(rs2))
        FleD(rd, rs1, rs2) => FleD(rd_fn(rd), rs_fn(rs1), rs_fn(rs2))
        FmvDX(rd, rs1) => FmvDX(rd_fn(rd), rs_fn(rs1))
        FmvXD(rd, rs1) => FmvXD(rd_fn(rd), rs_fn(rs1))
        La(rd, label) => La(rd_fn(rd), label)
        Li(rd, imm) => Li(rd_fn(rd), imm)
        Neg(rd, rs1) => Neg(rd_fn(rd), rs_fn(rs1))
        FnegD(rd, rs1) => FnegD(rd_fn(rd), rs_fn(rs1))
        Mv(rd, rs1) => Mv(rd_fn(rd), rs_fn(rs1))
        FmvD(rd, rs1) => FmvD(rd_fn(rd), rs_fn(rs1))
        Jalr(rs1) => Jalr(rs_fn(rs1))
        Jr(rs1) => Jr(rs_fn(rs1))
        t => t
    }
}