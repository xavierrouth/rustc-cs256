// skip-filecheck
// compile-flags: -Zdump-mir=all -Zmir-enable-passes=-GVN,+CopyProp,+ConstProp,+PartialRedundancyElimination,+ReorderBasicBlocks,+ReorderLocals,+AfterGVN,+ReferencePropagation
// unit-test: PartialRedundancyElimination

// EMIT_MIR pre_test_4.simple.PartialRedundancyElimination.diff
fn simple<T>(a: T, b: T) -> () {
  let mut x: i32 = 0;
  let mut y: i32 = 0;
  let mut z: i32 = 0;
  let mut c: i32 = 0;
  let mut w: i32 = 0;
  if (x >= 0) {
      x = w + c;
      y = w - c;
      z = x + y * c;
  } else {
      x = c + w;
      y = c - w;
      z = x + y + y + x;
  }
  z = x + y;
}

fn main() {
  simple::<u8>(4, 43);
  simple::<u16>(5, 266);
  simple::<u32>(3, 345);
  simple::<u64>(6, 34);
  simple::<u128>(7, 34);
  simple::<i8>(8, 43);
  simple::<i16>(9, 2645);
  simple::<i32>(10, -34);
  simple::<i64>(4363535, 2547256);
  simple::<i128>(436423664, 4574253754);
}