// skip-filecheck
// compile-flags: -Zdump-mir=all -Zmir-enable-passes=-GVN,+CopyProp,+ConstProp,+PartialRedundancyElimination,+ReorderBasicBlocks,+ReorderLocals,+AfterGVN,+ReferencePropagation
// unit-test: PartialRedundancyElimination


// EMIT_MIR pre_test_3.simple.PartialRedundancyElimination.diff
fn simple<T>(z: T) -> () {
    let mut x: i32 = 3;
    let mut y: i32 = 5;
    let a = 10;
    let b = 20;
    for i in 1..10 {
      if i % 2 == 0 {
        x += a + b;
        y += a - b;
      }
      else {
        y -= a + b;
        x += a - b;
      }
    }

    println!("{}", x);
    println!("{}", y);
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