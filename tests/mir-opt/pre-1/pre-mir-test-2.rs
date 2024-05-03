// skip-filecheck
// compile-flags: -Zdump-mir=all
// unit-test: PartialRedundancyElimination

#![feature(custom_mir, core_intrinsics)]
#![allow(unused_assignments)]
extern crate core;
use core::intrinsics::mir::*;

// EMIT_MIR pre_mir_test_2.simple.PartialRedundancyElimination.diff
#[custom_mir(dialect = "analysis", phase = "post-cleanup")]
fn simple(x: i32) -> i32 {
    mir!(
        let temp2: i32;

        {
            let temp1 = x;
            Goto(my_second_block)
        }

        my_second_block = {
            temp2 = Move(temp1);
            RET = temp2;
            Return()
        }
    )
}

pub fn main() {
    simple(0);
}