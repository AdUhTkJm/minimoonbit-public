
pub fn KnfEnv::extract(self: KnfEnv, s: @types.Syntax) -> @types.Syntax {
    ignore(self);
    match s {
        LetRec(z, w) => {
            if (w == Unit) {
                LetRec(z, App(Var("main"), []));
            } else {
                s;
            }
        }
        Let(a, b, w) => {
            if (w == Unit) {
                Let(a, b, App(Var("main"), []));
            } else {
                s;
            }
        }
        LetTuple(a, b, w) => {
            if (w == Unit) {
                LetTuple(a, b, App(Var("main"), []));
            } else {
                s;
            }
        }
        s => s
    }    
}
