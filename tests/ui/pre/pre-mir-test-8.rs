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
            let a = 10;
            let b = 20;
            let i = 5;
            Goto(bb1)
        }

        bb1 = {
            let t = x + y;
            Goto(bb2)
        }

        bb2 = {
            a = x + y;
            x = 10;
            b = x + y;
            Goto(bb3)
        }

        bb3 = {
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