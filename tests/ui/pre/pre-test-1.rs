// build-pass
// compile-flags: -Zdump_mir=main -Zmir-enable-passes=-GVN,+CopyProp,+ConstProp,+PartialRedundancyElimination

fn main() {
    let mut x: i32 = 0;
    let mut y: i32 = 0;
    let mut t: i32 = x + y;
    let mut f: i32 = t;
    if x >= y {
      f = x + y;
      f *= 2;
    }
    else {
      f = -(x + y) + 2;
    }

    println!("{}", f);
}