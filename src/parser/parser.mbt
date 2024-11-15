struct Tstream {
    // Current token we are looking at
    mut x: Int

    // All tokens
    mut tokens: Array[@lex.Token]
}

fn Tstream::expect(self: Tstream, t: @lex.Token) -> Unit {
    if (self.tokens[self.x].is(t).not()) {
        @util.die("Unexpected token \{self.tokens[self.x]} showed up, when \{t} is expected")
    }
    self.x += 1;
}

fn Tstream::check(self: Tstream, t: @lex.Token) -> Bool {
    if (self.tokens[self.x].is(t).not()) {
        return false;
    }
    self.x += 1;
    return true;
}

fn Tstream::peek(self: Tstream) -> @lex.Token {
    return self.tokens[self.x];
}

fn Tstream::retreat(self: Tstream) -> Unit {
    self.x -= 1;
}

fn Tstream::surround(self: Tstream) -> Array[@lex.Token] {
    let r: Array[@lex.Token] = [];
    for i = -5; i < 5; i = i + 1 {
        r.push(self.tokens[self.x + i]);
    }
    return r;
}

fn Tstream::consume(self: Tstream) -> @lex.Token {
    let t= self.tokens[self.x];
    self.x += 1;
    return t;
}

fn Tstream::identifier(self: Tstream) -> String {
    let ident = self.consume();
    let name = match ident {
        Ident(s) => s
        _ => @util.die("parser: expected identifier");
    }
    return name;
}

let tin: Tstream = Tstream::{ x : 0, tokens : [] };

fn pow(base: Int, exp: Int) -> Int64 {
    if (exp == 0) {
        1
    } else {
        pow(base, exp - 1) * base.to_int64();
    }
}
 
fn do_match() -> @types.Syntax {
    let matcher = expr();

    // the leading token Match is already consumed by primary()
    tin.expect(LBrace);

    let result: Array[@types.Branch] = [];
    while (tin.check(RBrace).not()) {
        let name = tin.identifier();

        let branch = @types.Branch :: { lead: name, binders: [], exec: Unit };

        if (tin.check(LPar)) {
            while (tin.check(RPar).not()) {
                let next = tin.consume();
                let name = match next {
                    Ident(s) => s
                    _ => @util.die("parser: expected identifier inside match")
                };

                branch.binders.push(name);
                if (tin.check(Comma).not() && tin.peek() != RPar) {
                    @util.die("')' expected");
                }
            }
        }

        tin.expect(Arrrow);

        branch.exec = expr();
        result.push(branch);
    }

    return Match(matcher, result);
}

fn primary() -> @types.Syntax {
    match tin.consume() {
        LitInt(x) => {
            if (tin.check(Dot)) {
                let z = tin.consume();
                match z {
                    LitInt(y) => Double(x.to_double() + y.to_double() / pow(10, y.to_string().length()).to_double())
                    _ => Double(x.to_double())
                }
            } else {
                Int(x)
            }
        }
        Ident(x) => Var(x)
        LPar => {
            let elem = [];
            while (tin.check(RPar).not()) {
                elem.push(expr());
                if (tin.check(Comma).not() && tin.peek() != RPar) {
                    @util.die("')' expected");
                }
            }
            match elem.length() {
                0 => Unit
                1 => elem[0]
                _ => Tuple(elem)
            }
        }
        True => Bool(true)
        False => Bool(false)
        Sub => Neg(expr(), ~kind = None)
        Not => {
            tin.expect(LPar);
            let z= expr();
            tin.expect(RPar);
            Not(z)
        }
        Array => {
            tin.expect(Colon);
            tin.expect(Colon);
            tin.expect(Make);
            tin.expect(LPar);
            let a1 = expr();
            tin.expect(Comma);
            let a2 = expr();
            tin.expect(RPar);
            Array(a1, a2)
        }
        LBrace => {
            let inner = stmt();
            tin.expect(RBrace);
            inner
        }
        Match => do_match()
        z => @util.die("Unexpected token \{z} in primary() with surrouding \{tin.surround()}")
    }
}

fn func() -> @types.Syntax {
    let mut x = primary();
    while (tin.peek() == LBrak || tin.peek() == LPar) {
        let n = tin.consume();

        // Function call
        if (n == LPar) {
            let result: Array[@types.Syntax] = [];
            while (tin.check(RPar).not()) {
                result.push(expr());
                if (tin.check(Comma).not() && tin.peek() != RPar) {
                    @util.die("Expected ')'");
                }
            }
            x = App(x, result);
        }

        // Get from array
        if (n == LBrak) {
            let inner = expr();
            tin.expect(RBrak);
            x = Get(x, inner);
        }
    }
    return x;
}

fn branch() -> @types.Syntax {
    if (tin.check(If)) {
        let cond = expr();
        tin.expect(LBrace);
        let body = stmt();
        tin.expect(RBrace);
        let mut otherwise: @types.Syntax = Unit;
        if (tin.check(Else)) {
            tin.expect(LBrace);
            otherwise = stmt();
            tin.expect(RBrace);
        }
        return If(cond, body, otherwise);
    }

    return func();
}

fn mul() -> @types.Syntax {
    let mut x = branch();
    while (tin.peek() == Mul || tin.peek() == Div) {
        let n = tin.consume();
        if (n == Mul) {
            x = Prim(x, branch(), @types.Mul, ~kind = None);
        }
        if (n == Div) {
            x = Prim(x, branch(), @types.Div, ~kind = None);
        }
    }
    return x;
}

fn add() -> @types.Syntax {
    let mut x = mul();
    while (tin.peek() == Add || tin.peek() == Sub) {
        let n = tin.consume();
        if (n == Add) {
            x = Prim(x, mul(), @types.Add, ~kind = None);
        }
        if (n == Sub) {
            x = Prim(x, mul(), @types.Sub, ~kind = None);
        }
    }
    return x;
}

fn expr() -> @types.Syntax {
    let mut x = add();
    while (tin.peek() == Equal || tin.peek() == Lequal) {
        let n = tin.consume();
        if (n == Equal) {
            x = Eq(x, add());
        }
        if (n == Lequal) {
            x = Le(x, add());
        }
    }
    return x;
}

fn get_type() -> @types.Type {
    let node_ty = tin.consume();
    let ty: @types.Type = match node_ty {
        Int => Int
        Double => Double
        Bool => Bool
        Unit => Unit
        Ident(s) => Type(s)
        LPar => {
            // Tuple?
            let arr: Array[@types.Type] = [];
            while (tin.check(RPar).not()) {
                arr.push(get_type());
                if (tin.check(Comma).not() && tin.peek() != RPar) {
                    @util.die("')' expected");
                }
            }

            // Function!
            if (tin.check(Arrow)) {
                Fun(arr, get_type())
            } else if (arr.length() == 1) {
                arr[0] // No 1-element tuple
            } else {
                Tuple(arr)
            }
        }
        Array => {
            tin.expect(LBrak);
            let ty = get_type();
            tin.expect(RBrak);
            Array(ty)
        }
        _ => @util.die("Expected type, but got \{tin.peek()}")

    }
    return ty;
}

fn stmt() -> @types.Syntax {
    if (tin.peek() == Let) {
        ignore(tin.consume());
        
        // Tuple
        if (tin.peek() == LPar) {
            ignore(tin.consume());
            let vars: Array[String] = [];
            while (tin.check(RPar).not()) {
                let name = tin.identifier();
                vars.push(name);
                if (tin.check(Comma).not() && tin.peek() != RPar) {
                    @util.die("Bad tuple in 'let' statement")
                }
            }

            let mut ty: @types.Type = Var(Ref::new(None));
            let mut annotated = false;
            if (tin.check(Colon)) {
                ty = Var(Ref::new(Some(get_type())));
                annotated = true;
            }

            tin.expect(Assign);
            let node = expr();

            tin.expect(Semicolon);
            if (annotated) {
                let tarr = match ty {
                    Tuple(arr) => arr
                    _ => @util.die("Must be a tuple type in let-tuple structure")
                }
                let zipped = vars.mapi(fn (i, z) { (z, tarr[i]) });
                return LetTuple(zipped, node, stmt());
            } else {
                return LetTuple(vars.map(fn (z) { (z, Var(Ref::new(None))) }), node, stmt());
            }
        }

        // Ordinary let
        let name = tin.identifier();

        let mut ty: @types.Type = Var(Ref::new(None));
        if (tin.check(Colon)) {
            ty = Var(Ref::new(Some(get_type())));
        }

        tin.expect(Assign);
        let node = expr();

        tin.expect(Semicolon);

        return Let((name, ty), node, stmt());
    }

    if (tin.peek() == Fn) {
        ignore(tin.consume());
        let f_name = tin.identifier();

        tin.expect(LPar);
        let fargs: Array[(String, @types.Type)] = [];
        while (tin.check(RPar).not()) {
            let v_i = tin.consume();
            let v_name = match v_i {
                Ident(s) => s
                _ => @util.die("Expected identifier in function argument");
            }
            let mut ty: @types.Type = Var(Ref::new(None));
            if (tin.check(Colon)) {
                ty = Var(Ref::new(Some(get_type())));
            }

            fargs.push((v_name, ty));
            if (tin.peek() == Comma) {
                ignore(tin.consume());
            } else if (tin.peek() != RPar) {
                @util.die("')' expected");
            }
        }

        let mut ret_ty: @types.Type = Var(Ref::new(None));
        if (tin.check(Arrow)) {
            ret_ty = Var(Ref::new(Some(get_type())));
        }

        tin.expect(LBrace);
        let fbody = stmt();
        tin.expect(RBrace);
        tin.expect(Semicolon);

        return LetRec(@types.Fundef::{
            name: (f_name, Fun(fargs.map(fn (z) {z.1;}), ret_ty)),
            args: fargs, body: fbody }, stmt());
    }

    let w = expr();

    match w {
        Get(x, inner) => {
            if (tin.check(Assign).not()) {
                return w;
            }
            let assign = expr();
            tin.expect(Semicolon);
            return Let(("_", Unit), Put(x, inner, assign), stmt());
        }
        _ => return w;
    }
}

fn toplevel_fn() -> @types.Syntax {
    let f_name = tin.identifier();
    
    let fargs: Array[(String, @types.Type)] = [];
    let mut ret_ty: @types.Type = Unit;
    if (f_name != "main" && f_name != "init") {
        tin.expect(LPar);
        while (tin.check(RPar).not()) {
            let v_i = tin.consume();
            let v_name = match v_i {
                Ident(s) => s
                _ => @util.die("Expected identifier in function argument");
            }
            tin.expect(Colon);
            let ty = get_type();

            fargs.push((v_name, ty));
            if (tin.peek() == Comma) {
                ignore(tin.consume());
            } else if (tin.peek() != RPar) {
                @util.die("')' expected");
            }
        }
        
        tin.expect(Arrow);
        ret_ty = get_type();
    }
    tin.expect(LBrace);
    let fbody = stmt();
    tin.expect(RBrace);
    tin.expect(Semicolon);

    return LetRec(@types.Fundef::{
        name: (f_name, Fun(fargs.map(fn (z) {z.1;}), ret_ty)),
        args: fargs, body: fbody }, toplevel());
}

fn toplevel_let() -> @types.Syntax {
    let name = tin.identifier();

    tin.expect(Colon);
    let ty = get_type();

    tin.expect(Assign);
    let node = expr();

    tin.expect(Semicolon);

    return Let((name, ty), node, toplevel());
}

fn toplevel_enum() -> @types.Syntax {
    let name = tin.identifier();
    let elems = [];

    tin.expect(LBrace);
    while (tin.check(RBrace).not()) {
        let next = tin.identifier();

        if (tin.check(LPar).not()) {
            elems.push(@types.EnumEntry :: { name: next, binders: [] });
            continue;
        }

        let binders = [];
        while (tin.check(RPar).not()) {
            let ty = get_type();
            binders.push(ty);
            if (tin.check(Comma).not() && tin.peek() != RPar) {
                @util.die("')' expected");
            }
        }

        elems.push(@types.EnumEntry :: { name: next, binders: binders });
    }

    tin.expect(Semicolon);

    return Enum(name, elems, toplevel());
}

pub let global: Array[String] = [];

fn toplevel() -> @types.Syntax {
    let n = tin.consume();

    if (n == Fn) {
        return toplevel_fn();
    }

    if (n == Let) {
        return toplevel_let();
    }

    if (n == Enum) {
        return toplevel_enum();
    }

    if (n == EOF) {
        // Add a main call here;
        // we need to eliminate the main call for WASM and RISC-V,
        // but this has to be present for KNF interpreter and JS
        return App(Var("main"), []);
    }

    @util.die("Unexpected token at toplevel: \{n}");
}

pub fn parse(tks: Array[@lex.Token]) -> @types.Syntax {
    tin.tokens = tks;

    return toplevel();
}

// Add internal things
pub fn augment(s: @types.Syntax) -> @types.Syntax {
    LetRec(@types.Fundef:: { name: ("print_int", Fun([Int], Unit)), args: [("x", Int)], body:
        ApplyExtern("minimbt_print_int", [Var("x")])}, 
    LetRec(@types.Fundef:: { name: ("print_endline", Fun([], Unit)), args: [], body:
        ApplyExtern("minimbt_print_endline", [])},
    LetRec(@types.Fundef:: { name: ("truncate", Fun([Double], Int)), args: [("x", Double)], body:
        ApplyExtern("minimbt_truncate", [Var("x")])},
    LetRec(@types.Fundef:: { name: ("print_char", Fun([Int], Unit)), args: [("x", Int)], body:
        ApplyExtern("minimbt_print_char", [Var("x")])}, 
    LetRec(@types.Fundef:: { name: ("read_int", Fun([], Int)), args: [], body:
        ApplyExtern("minimbt_read_int", [])},
    LetRec(@types.Fundef:: { name: ("read_char", Fun([], Int)), args: [], body:
        ApplyExtern("minimbt_read_char", [])},
    LetRec(@types.Fundef:: { name: ("int_of_float", Fun([Double], Int)), args: [("x", Double)], body:
        ApplyExtern("minimbt_int_of_float", [Var("x")])},
    LetRec(@types.Fundef:: { name: ("float_of_int", Fun([Int], Double)), args: [("x", Int)], body:
        ApplyExtern("minimbt_float_of_int", [Var("x")])},
    LetRec(@types.Fundef:: { name: ("sin", Fun([Double], Double)), args: [("x", Double)], body:
        ApplyExtern("minimbt_sin", [Var("x")])},
    LetRec(@types.Fundef:: { name: ("cos", Fun([Double], Double)), args: [("x", Double)], body:
        ApplyExtern("minimbt_cos", [Var("x")])},
    LetRec(@types.Fundef:: { name: ("atan", Fun([Double], Double)), args: [("x", Double)], body:
        ApplyExtern("minimbt_atan", [Var("x")])},
    LetRec(@types.Fundef:: { name: ("abs_float", Fun([Double], Double)), args: [("x", Double)], body:
        ApplyExtern("minimbt_abs_float", [Var("x")])},
    LetRec(@types.Fundef:: { name: ("sqrt", Fun([Double], Double)), args: [("x", Double)], body:
        ApplyExtern("minimbt_sqrt", [Var("x")])},
    LetRec(@types.Fundef:: { name: ("floor", Fun([Double], Double)), args: [("x", Double)], body:
        ApplyExtern("minimbt_floor", [Var("x")])}, s
    ))))))))))))))
}