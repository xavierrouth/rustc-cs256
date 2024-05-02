// build-pass
// compile-flags: -Zdump_mir=simple -Zdump-mir-dataflow=y -Zmir-opt-level=0 -Zmir-enable-passes=+PartialRedundancyElimination,-SimplifyCfg-elaborate-drops

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
            let b = 10;
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