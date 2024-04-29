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
            let x = 3;
            let y = 5;
            let b = x + y;
            Goto(half)
        }

        half = {
            // let a = x + y;
            Goto(second)
        }

        second = {
            // a = x + y;
            b = 20;
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