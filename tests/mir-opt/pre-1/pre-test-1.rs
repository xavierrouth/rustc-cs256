// skip-filecheck
// compile-flags: -Zdump-mir=all -Zmir-enable-passes=-GVN,+CopyProp,+ConstProp,+PartialRedundancyElimination,+ReorderBasicBlocks,+ReorderLocals,+AfterGVN,+ReferencePropagation
// unit-test: PartialRedundancyElimination


// EMIT_MIR pre_test_1.simple.PartialRedundancyElimination.diff
fn simple(a: i32) -> () {
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
    simple(3)
}