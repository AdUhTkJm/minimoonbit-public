pub fn print_functions(asm : Array[AssemblyFunction]) -> String {
    let logger = Buffer::new()

    for f in asm {
        f.output(logger)
        logger.write_string("\n")
    }

    emit_global(logger);
    emit_externals(logger);
    
    return logger.to_string();
}
