// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"() ({
        %one = "llvm.constant"() <{ "value" = 1 : i64 }> : () -> i32
        %two = "llvm.constant"() <{ "value" = 2 : i64 }> : () -> i32
    }) : () -> ()
}) : () -> ()
