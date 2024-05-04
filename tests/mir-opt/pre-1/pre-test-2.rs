// Generics spam
// skip-filecheck
// compile-flags: -Zdump-mir=all -Zmir-enable-passes=-GVN,+CopyProp,+ConstProp,+PartialRedundancyElimination,+ReorderBasicBlocks,+ReorderLocals,+AfterGVN,+ReferencePropagation
// unit-test: PartialRedundancyElimination


// EMIT_MIR pre_test_2.simple.PartialRedundancyElimination.diff
fn simple<T>(a: T) -> () {
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
    simple::<u8>(4);
    simple::<u16>(5);
    simple::<u32>(3);
    simple::<u64>(6);
    simple::<u128>(7);
    simple::<i8>(8);
    simple::<i16>(9);
    simple::<i32>(10);
    simple::<i64>(11);
    simple::<i128>(12);
}