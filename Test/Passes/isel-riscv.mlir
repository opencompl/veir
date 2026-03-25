// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
^bb0():
    %one = "llvm.constant"() <{ "value" = 1 : i64 }> : () -> i64
    %two = "llvm.constant"() <{ "value" = 2 : i64 }> : () -> i64
    // CHECK:      %{{.*}} = "riscv.li"() <{"value" = 1 : i64}> : () -> i64
    // CHECK-NEXT: %{{.*}} = "riscv.li"() <{"value" = 2 : i64}> : () -> i64
}) : () -> ()
