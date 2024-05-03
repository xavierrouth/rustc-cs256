// skip-filecheck
// compile-flags: -Zdump-mir=all
// unit-test: PartialRedundancyElimination

#![feature(custom_mir, core_intrinsics)]
#![allow(unused_assignments)]
extern crate core;
use core::intrinsics::mir::*;

// EMIT_MIR pre_mir_test_6.simple.PartialRedundancyElimination.after.mir
#[custom_mir(dialect = "analysis", phase = "post-cleanup")]
fn simple(c: i32) -> i32 {
    mir!(

        {
            let x: i32 = 3;
            let y: i32 = 5;
            let a = 10;
            let b = 10;
            let c = true;
            Goto(branch)
        }
        
        branch = { 
            a = x + y;
            match c {
                true => t1,
                _ => f1,
            }
        }

        t1 = {
            Goto(t)
        }

        t = {
            a = x + y;
            Goto(output)
        }

        f1 = {
            Goto(f)
        }

        f = {
            b = x + y;
            Goto(output)
        }

        output = {
            RET = x + y;
            Return()
        }
    )
}

pub fn main() {
    simple(0);
}