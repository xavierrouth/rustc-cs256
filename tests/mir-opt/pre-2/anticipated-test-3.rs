// skip-filecheck
// unit-test: PartialRedundancyElimination

#![feature(custom_mir, core_intrinsics)]
#![allow(unused_assignments)]
extern crate core;
use core::intrinsics::mir::*;

#[custom_mir(dialect = "analysis", phase = "post-cleanup")]
fn simple(c: i32) -> i32 {
    mir!(

        {
            let x = 3;
            let y = 5;
            let b = x + y;
            Goto(half)
        }

        half = {
            Goto(second)
        }

        second = {
            let a = x + y;
            x = 30;
            Goto(output)
        }

        output = {
             RET = 10;
            Return()
        }
    )
}

pub fn main() {
    simple(0);
}