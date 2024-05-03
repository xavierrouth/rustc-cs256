// skip-filecheck
// compile-flags: -Zdump-mir=all
// unit-test: PartialRedundancyElimination

#![feature(custom_mir, core_intrinsics)]
#![allow(unused_assignments)]
extern crate core;
use core::intrinsics::mir::*;

// EMIT_MIR pre_mir_test_9.simple.PartialRedundancyElimination.after.mir
#[custom_mir(dialect = "analysis", phase = "post-cleanup")]
fn simple(c: i32) -> i32 {
    mir!(

        {
            let x: i32 = 3;
            let y: i32 = 5;
            let a = 10;
            let b = 20;
            let i = 5;
            Goto(loop_preheader)
        }

        loop_preheader = {
            Goto(loop_header)
        }

        loop_header = {
            let c = i < 20;

            match c {
                true => loop_body,
                _ => loop_exit,
            }
        }

        loop_body = {
            i = i + 1;
            a = x + y;
            Goto(loop_second_body)
        }

        loop_second_body = {

            Goto(loop_header)
        }

        loop_exit = {
            a = x + y;
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