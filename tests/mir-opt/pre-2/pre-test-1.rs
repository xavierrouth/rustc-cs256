// build-pass
// compile-flags: -Zdump_mir=aaa -Zdump-mir-dataflow=y -Zmir-enable-passes=-GVN,+CopyProp,+ConstProp,+PartialRedundancyElimination,+ReorderBasicBlocks,+ReorderLocals,+AfterGVN,+ReferencePropagation

fn aaa(a: i32) -> () {
    let mut x: i32 = 0;
    let mut y: i32 = 0;
    let mut t: i32 = 0;
    let mut f: i32 = t;
    if x >= y {
        f = x + y;
        f *= 2;
    } else {
        f = -(x + y) + 2;
    }

    t = x + y;

    println!("{}", f);
    println!("{}", t);
}

fn main() {
    aaa(3)
}