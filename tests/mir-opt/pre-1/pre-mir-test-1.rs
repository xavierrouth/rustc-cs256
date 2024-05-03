// skip-filecheck
// compile-flags: -Zdump-mir=all
// unit-test: PartialRedundancyElimination


#![feature(custom_mir, core_intrinsics)]
#![allow(unused_assignments)]
extern crate core;
use core::intrinsics::mir::*;

// EMIT_MIR pre_mir_test_1.simple.PartialRedundancyElimination.after.mir
#[custom_mir(dialect = "analysis", phase = "post-cleanup")]
fn simple(c: bool) -> bool {
    mir!({
        let a = c;
        RET = true;
        Return()
    })
}

fn main() {
    assert_eq!(true, simple(true));
}