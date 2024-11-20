let i: Array[Int] = Array::make(6, 0);
fn g(s:Int) -> Unit {
  fn f(x: Int) -> Int {
    if (i[x] == 0) {
      let _ = g(s-1);
      x
    } else {
      i[x] = i[x] - 1;
      i[x] + f(i[x])
    }
  };
  if(s == 0) {
    ()
  } else {
    println(f(s))
  }
};

fn main {
  i[1] = 3;
  i[2] = 4;
  i[3] = 5;
  i[4] = 2;
  i[5] = 1;
  g(5)
};