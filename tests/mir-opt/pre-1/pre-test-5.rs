// Generics spam
// skip-filecheck
// compile-flags: -Zdump-mir=all -Zmir-enable-passes=-GVN,+CopyProp,+ConstProp,+PartialRedundancyElimination,+ReorderBasicBlocks,+ReorderLocals,+AfterGVN,+ReferencePropagation
// unit-test: PartialRedundancyElimination


// EMIT_MIR pre_test_5.simple.PartialRedundancyElimination.diff
fn simple<T>(_z: T) -> () {
  let mut x: i32 = 3;
  let mut y: i32 = 5;
  let mut a = 10;
  let mut b = 20;
  let mut i = 0;
  while i < a {
    if (i - a > b - i) {
      b = x + y;
      a = x - y;
    }
    x = x + y;
    y = a + b;
    if x > y {
      x += a + b;
    }
    else {
      x -= a + b;
    }
    i += 1;
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