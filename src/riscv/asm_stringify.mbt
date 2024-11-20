pub fn print_functions(asm : Array[AssemblyFunction]) -> String {
    let logger = Buffer::new()

    for f in asm {
        f.output(logger)
        logger.write_string("\n")
    }

    emit_enums(logger);

    emit_global(logger);
    emit_externals(logger);
    emit_matches(logger);
    
    emit_bss(logger);
    
    return logger.to_string();
}
