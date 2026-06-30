// RUN: veir-opt %s -pgrp=riscv | filecheck %s

"builtin.module"() ({
    "func.func"()  <{function_type = (i64, i64) -> i64}> ({
    ^bb(%a: i64, %b: i64):
        %add = "llvm.add"(%a, %b) : (i64, i64) -> i64
        // CHECK: %{{.*}} = "riscv.add"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "func.return"(%add) : (i64) -> ()
    }) : () -> ()
}) : () -> ()
