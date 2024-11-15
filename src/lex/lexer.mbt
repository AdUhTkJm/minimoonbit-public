pub enum Token {
    Add
    Sub
    Mul
    Div
    LPar        // (
    RPar        // )
    Fn
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
    Ident(String)
    LitInt(Int)
    EOF
} derive (Show, Eq)

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
                @util.die("Lexing error: '<' must be followed by '='");
            }

            
            '/' => if arr[x + 1] == '/' {
                while (arr[x] != '\n') {
                    x += 1;
                }
            } else {
                result.push(Div);
            }

            '\x00' => ()
            _ => @util.die("Lexing error: \{c} (with int \{c.to_int()})");
        }
        x += 1;
    }

    result.push(EOF);
    return result;
}