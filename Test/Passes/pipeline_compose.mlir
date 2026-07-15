// RUN: veir-opt %s -p=canonicalize -pgrp=riscv -p=cse -p=dce | filecheck %s

// Check that -p and -pgrp compose: repeated and mixed flags build one pipeline
// in the order the flags appear on the command line.

"builtin.module"() ({
    "func.func"()  <{function_type = (i64, i64) -> i64}> ({
    ^bb(%a: i64, %b: i64):
        %add = "llvm.add"(%a, %b) : (i64, i64) -> i64
        // CHECK: %{{.*}} = "riscv.add"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "func.return"(%add) : (i64) -> ()
    }) : () -> ()
}) : () -> ()
