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
            let x: i32 = 3;
            let y: i32 = 5;
            let a = 10;
            let c = true;
            Goto(branch)
        }
        
        branch = { 
            match c {
                true => t,
                _ => f,
            }
        }

        t = {
            a = x + y;
            Goto(output)
        }

        f = {
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