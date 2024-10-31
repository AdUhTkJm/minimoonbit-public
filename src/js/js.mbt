let vars: Array[String] = [];
fn eval(x: @types.Syntax) -> String {
    match x {
        Int(x) => x.to_string()
        Double(x) => x.to_string()
        Bool(x) => x.to_string()
        Var(x) => x.to_string()
        Unit => "null"
        Not(x) => "!(\{eval(x)})"
        Neg(x, ..) => "-(\{eval(x)})"
        Array(len, elem) =>
            "(function() { var __t = Array(\{eval(len)}), __e = (\{eval(elem)}); for (var __i = 0; __i < \{len}; __i++) __t[__i] = __e; return __t; })()"
        Tuple(arr) => "[" + arr.map(eval).join(", ") + "]"
        Get(x, i) => "(\{eval(x)})[\{eval(i)}]"
        Put(x, i, v) => "((\{eval(x)})[\{eval(i)}] = (\{eval(v)}), null)"

        Prim(a, b, op, ~kind = _) => match op {
            Add => "(\{eval(a)} + \{eval(b)})"
            Sub => "(\{eval(a)} - \{eval(b)})"
            Mul => "(\{eval(a)} * \{eval(b)})"
            Div => "(\{eval(a)} / \{eval(b)})"
        }

        If(cond, body, otherwise) =>
            "(function() { if (\{eval(cond)}) return (\{eval(body)}); else return (\{eval(otherwise)}) })()"

        Eq(a, b) => "(\{eval(a)} == \{eval(b)})"
        LE(a, b) => "(\{eval(a)} <= \{eval(b)})"

        Let((a, _), val, w) =>
            "(function() { var \{a} = (\{eval(val)}); \nreturn \{eval(w)} })()"
        
        LetRec({ name: (f_name, _), args: args, body: syn }, w) => {
            let arg_names = args.map(fn (x) { x.0 }).join(", ");
            "(function() { var \{f_name} = function(\{arg_names}) { return (\{eval(syn)}) }; return \{eval(w)} })()"
        }

        LetTuple(arr, val, w) =>
            arr.foldi(~init = "", fn (i, total, x) { 
                total + "; \{x} = \{val}[\{i}]"    
            }) + "\{eval(w)}";


        App(name, args)=> {
            let list = args.map(eval).join(", ");
            "\{eval(name)}(\{list})"
        }
        ApplyExtern(name, args)=> {
            let list = args.map(eval).join(", ");
            "\{name}(\{list})"
        }

    }
}

pub fn emit(program: @types.Syntax) -> String {
    return "(function() {\{eval(program)}})()";
}