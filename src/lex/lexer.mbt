pub enum Token {
    Add
    Sub
    Mul
    Div
    LPar        // (
    RPar        // )
    Fn
    Define
    Enifed
    Let
    Colon
    Arrow       // ->
    Arrrow      // =>
    Comma
    LBrace      // {
    RBrace      // }
    Int
    Double
    Semicolon
    Assign
    Bool
    True
    Unit
    False
    Array
    Make
    LBrak       // [
    RBrak       // ]
    Dot
    Equal
    Lequal
    If
    Else
    Not
    Enum
    Match
    Template
    Of
    End
    Ident(String)
    LitInt(Int)
    EOF
} derive (Show, Eq, Hash)

// Only checks for type, nothing else.
pub fn Token::is(self: Token, other: Token) -> Bool {
    if (self == other) {
        return true;
    }
    match (self, other) {
        (Ident(_), Ident(_)) => true
        (LitInt(_), LitInt(_)) => true
        _ => false
    }
}


let macro: Map[Token, (Array[Token], Array[Token])] = Map::new();

pub fn is_digit(c: Char) -> Bool {
    return ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9'].contains(c);
}

fn is_ident(c: Char) -> Bool {
    return "AaBbCcDdEeFfGgHhIiJjKkLlMmNnOoPpQqRrSsTtUuVvWwXxYyZz_".contains_char(c);
}

fn is_space(c: Char) -> Bool {
    return [' ', '\n', '\t', '\r'].contains(c);
}

fn distinguish(z: Array[Char]) -> Token {
    let y = z.fold(~init = "", fn (s, c) { s + c.to_string() });
    match y {
        "fn" => Fn
        "define" => Define
        "enifed" => Enifed
        "let" => Let
        "Int" => Int
        "Double" => Double
        "Bool" => Bool
        "true" => True
        "Unit" => Unit
        "false" => False
        "Array" => Array
        "make" => Make
        "if" => If
        "else" => Else
        "not" => Not
        "enum" => Enum
        "match" => Match
        "template" => Template
        "of" => Of
        "end" => End
        _ => Ident(y)
    }
}

pub fn lex(input: String) -> Array[Token] {
    let arr = input.iter().to_array();
    arr.push('\x00');

    let result: Array[Token] = [];
    let mut x = 0;
    while (x < arr.length()) {
        let c = arr[x];

        if is_space(c) {
            x += 1;
            continue;
        }

        if is_digit(c) {
            let mut z = 0;
            while (is_digit(arr[x])) {
                z = z * 10 + arr[x].to_int() - '0'.to_int();
                x += 1;
            }
            result.push(LitInt(z));
            continue;
        }

        if is_ident(c) {
            let z: Array[Char] = [];
            while (is_ident(arr[x]) || is_digit(arr[x])) {
                z.push(arr[x]);
                x += 1;
            }
            result.push(distinguish(z));
            continue;
        }
        match c {
            '+' => result.push(Add)
            '*' => result.push(Mul)
            '.' => result.push(Dot)
            '(' => result.push(LPar)
            ')' => result.push(RPar)
            ':' => result.push(Colon)
            '[' => result.push(LBrak)
            ']' => result.push(RBrak)
            ',' => result.push(Comma)
            '{' => result.push(LBrace)
            '}' => result.push(RBrace)
            ';' => result.push(Semicolon)

            // More possibilities
            '-' => if arr[x + 1] == '>' {
                result.push(Arrow);
                x += 1;
            } else {
                result.push(Sub);
            }
            
            '=' => if arr[x + 1] == '=' {
                result.push(Equal);
                x += 1;
            } else if arr[x + 1] == '>' {
                result.push(Arrrow);
                x += 1;
            } else {
                result.push(Assign);
            }

            '<' => if arr[x + 1] == '=' {
                result.push(Lequal);
                x += 1;
            } else {
                @util.die("lex: '<' must be followed by '='");
            }

            
            '/' => if arr[x + 1] == '/' {
                while (arr[x] != '\n') {
                    x += 1;
                }
            } else {
                result.push(Div);
            }

            '\x00' => ()
            _ => @util.die("lex: \{c} (with int \{c.to_int()})");
        }
        x += 1;
    }
    
    let mut st = 0;
    let name: Array[Token] = [];
    let tokens: Array[Token] = [];
    let mid_result: Array[Token] = [];

    for x in result {
        if(x == Define) {
            if(st != 0) {
                @util.die("lex: define, ':' and enifed must match");
            }
            st = 1;
            continue;
        }
        if(x == Colon && st == 1) {
            st = 2;
            continue;
        }
        if(x == Enifed) {
            if(st != 2) {
                @util.die("lex: define, ':' and enifed must match");
            }
            let args: Array[Token] = [];
            if(name.length() != 1) {
                if(name.length() < 4 || name.length()%2 != 0) {
                    @util.die("lex: invalid arguments");
                }
                if(name[1]!=LPar || name[name.length()-1]!=RPar) {
                    @util.die("lex: parentheses don't match");
                }
                let mut i = 2;
                while i < name.length() - 1 {
                    if(i % 2 == 0){
                        match name[i] {
                            Ident(_) => ()
                            _ => @util.die("lex: arguments not match");
                        }
                        args.push(name[i]);
                    } else {
                        if(name[i] != Comma) {
                            @util.die("lex: arguments not match");
                        }
                    }
                    i += 1;
                }
            }
            macro[name[0]] = (args, tokens);
            st = 0;
            continue;
        }
        if (st == 0) {
            mid_result.push(x);
        }
        if (st == 1) {
            name.push(x);
        }
        if (st == 2){
            tokens.push(x);
        }
    }
    if(st != 0) {
        @util.die("lex: define, ':' and enifed must match");
    }
    
    let final_result = mid_result
        |> macro_process
        |> template_process;

    final_result.push(EOF);
    return final_result;
}

fn macro_process(mid_result: Array[Token]) -> Array[Token] {
    let final_result: Array[Token] = [];

    let mut i = 0;
    let mid_len = mid_result.length();
    while i < mid_len {
        let x = mid_result[i];
        if (macro.contains(x)) {
            let (args, tokens) = macro[x].unwrap();
            let len = args.length();
            if (len == 0) {
                final_result.append(tokens);
                i += 1;
                continue;
            }
            i += 1;
            if (i >= mid_len || mid_result[i] != LPar) {
                @util.die("lex: macro must be followed by (");
            }
            i += 1;
            let map_token: Map[Token, Array[Token]] = Map::new();
            let mut j = 0;
            while j < len {
                let arr_token: Array[Token] = [];
                if(j < len - 1){
                    while (i < mid_len && mid_result[i] != Comma){
                        arr_token.push(mid_result[i]);
                        i += 1;
                    }
                }
                else{
                    while (i < mid_len && mid_result[i] != RPar){
                        arr_token.push(mid_result[i]);
                        i += 1;
                    }
                }
                i += 1;
                if(arr_token.length() == 0 || i >= mid_len) {
                    @util.die("lex: invalid arguments");
                }
                map_token[args[j]] = arr_token;
                j += 1;
            }
            for x in tokens {
                if(map_token.contains(x)) {
                    final_result.append(map_token[x].unwrap());
                } else {
                    final_result.push(x);
                }
            }
            continue;
        } else {
            final_result.push(x);
        }
        i += 1;
    }
    

    return final_result;
}

fn template_process(body: Array[Token]) -> Array[Token] {
    macro.clear();

    let mut i = 0;
    while (i < body.length()) {
        if (body[i] == Template) {
            let def = [LBrace, Fn];

            let id = match body[i + 1] {
                Ident(s) => s
                _ => @util.die("lex: identifier expected after template")
            }
            def.push(Ident("__templated_" + id));

            if (body[i + 2] != Of) {
                @util.die("lex: expected 'of'");
            }
            i += 3;

            let args = [];
            while (body[i] != Colon) {
                args.push(body[i]);
                if (body[i + 1] != Comma && body[i + 1] != Colon) {
                    @util.die("lex: expected ',' or ':', but seen \{body[i + 1]}");
                } else {
                    i += 1;
                }
            }

            let mut j = i + 1;
            while (body[j] != End) {
                def.push(body[j]);
                j += 1;
            }

            def.append([Ident("__templated_" + id), RBrace]);

            macro[Ident(id)] = (args, def);
        }
        i += 1;
    }
    
    // Delete the template part
    let result = [];
    let mut in_template = false;
    for x in body {
        match x {
            End => in_template = false;
            Template => in_template = true;
            s => if (in_template.not()) { result.push(s); }
        }
    }
    
    return result |> macro_process;
}