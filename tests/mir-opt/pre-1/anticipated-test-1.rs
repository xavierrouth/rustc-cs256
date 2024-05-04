// skip-filecheck
// compile-flags: -Zdump-mir=all
// unit-test: PartialRedundancyElimination

#![feature(custom_mir, core_intrinsics)]
#![allow(unused_assignments)]
extern crate core;
use core::intrinsics::mir::*;

// EMIT_MIR anticipated_test_1.simple.PartialRedundancyElimination.after.mir
#[custom_mir(dialect = "analysis", phase = "post-cleanup")]
fn simple(c: i32) -> i32 {
    mir!(

        {
            let x = 3;
            let y = 5;
            Goto(second)
        }

        second = {

            let a = x + y;
            Goto(output)
        }

        output = {
            RET = a;
            Return()
        }
    )
}

pub fn main() {
    simple(0);
}