fn int_f(logger: Logger, name: String) -> Unit {
    logger.write_string("\{name}:\n    j minimbt_\{name}\n\n");
}

fn double_f(logger: Logger, name: String) -> Unit {
    logger.write_string("\{name}:\n");
    logger.write_string("    addi sp, sp, -16\n");
    logger.write_string("    sd ra, 0(sp)\n");
    logger.write_string("    fmv.d.x fa0, a0\n");
    logger.write_string("    call minimbt_\{name}\n");
    logger.write_string("    fmv.x.d a0, fa0\n");
    logger.write_string("    ld ra, 0(sp)\n");
    logger.write_string("    addi sp, sp, 16\n");
    logger.write_string("    ret\n\n");
}

pub fn print_functions(asm : Array[AssemblyFunction]) -> String {
    let logger = Buffer::new()

    // Output all external functions at this stage
    ignore([
        "print_int", "read_int", "print_char", "read_char", "print_endline"
    ].map(fn (x) { int_f(logger, x); }));

    ignore([
        "sin", "cos", "atan", "abs_float", "sqrt", "floor"
    ].map(fn (x) { double_f(logger, x); }));

    // These three are different
    // truncate is the same as int_of_float
    logger.write_string("int_of_float:\n");
    logger.write_string("truncate:\n");
    logger.write_string("    addi sp, sp, -16\n");
    logger.write_string("    sd ra, 0(sp)\n");
    logger.write_string("    fmv.d.x fa0, a0\n");
    logger.write_string("    call minimbt_int_of_float\n");
    logger.write_string("    ld ra, 0(sp)\n");
    logger.write_string("    addi sp, sp, 16\n");
    logger.write_string("    ret\n\n");

    
    logger.write_string("float_of_int:\n");
    logger.write_string("    addi sp, sp, -16\n");
    logger.write_string("    sd ra, 0(sp)\n");
    logger.write_string("    call minimbt_float_of_int\n");
    logger.write_string("    fmv.x.d a0, fa0\n");
    logger.write_string("    ld ra, 0(sp)\n");
    logger.write_string("    addi sp, sp, 16\n");
    logger.write_string("    ret\n\n");

    for f in asm {
        f.output(logger)
        logger.write_string("\n")
    }

    emit_global(logger);
    
    return logger.to_string();
}
