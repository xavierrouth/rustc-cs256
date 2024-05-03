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
            let b = 1;
            let q = true;
            let r = false;
            Goto(branch)
        }

        branch = { 
            match q {
                true => t1,
                _ => f1,
            }
        }

        t1 = {
            Goto(t2)
        }

        t2 = {
            Goto(t3)
        }

        t3 = {
            match r {
                true => t4,
                _ => t2,
            }
        }

        t4 = {
            Goto(out)
        }

        f1 = {
            let x = b + c;
            Goto(f2)
        }

        f2 = {
            Goto(f3)
        }

        f3 = {
            Goto(out)
        }

        out = {
            let y = b + c;
            Goto(output)
        }

        output = {
            RET = 19;
            Return()
        }
    )
}

pub fn main() {
    simple(0);
}