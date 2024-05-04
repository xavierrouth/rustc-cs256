// build-pass
// compile-flags: -Zdump_mir=simple -Zdump-mir-dataflow=y -Zmir-opt-level=0 -Zmir-enable-passes=+PartialRedundancyElimination,-SimplifyCFG,-SimplifyCfg-elaborate-drops
// -Zmir-enable-passes=-GVN,+CopyProp,+ConstProp,+PartialRedundancyElimination,+ReorderBasicBlocks,+ReorderLocals,+AfterGVN,ReferencePropagation,
// -Zmir-opt-level=0

#![feature(custom_mir, core_intrinsics)]
#![allow(unused_assignments)]
extern crate core;
use core::intrinsics::mir::*;

#[custom_mir(dialect = "analysis", phase = "post-cleanup")]
pub fn simple(x: i32) -> i32 {
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