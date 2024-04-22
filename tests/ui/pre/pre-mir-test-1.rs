// build-pass
// compile-flags: -Zdump_mir=f -Zmir-opt-level=0 -Zmir-enable-passes=+PartialRedundancyElimination
// -Zmir-enable-passes=-GVN,+CopyProp,+ConstProp,+PartialRedundancyElimination,+ReorderBasicBlocks,+ReorderLocals,+AfterGVN,ReferencePropagation,
// -Zmir-opt-level=0

#![feature(custom_mir, core_intrinsics)]
#![allow(unused_assignments)]
extern crate core;
use core::intrinsics::mir::*;

#[custom_mir(dialect = "analysis", phase = "post-cleanup")]
fn f(c: bool) -> bool {
    mir!({
        let a = c;
        RET = true;
        Return()
    })
}

fn main() {
    assert_eq!(true, f(true));
}