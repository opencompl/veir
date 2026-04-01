// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"() ({
        %one = "llvm.constant"() <{ "value" = 1 : i64 }> : () -> i8
        %two = "llvm.constant"() <{ "value" = 2 : i64 }> : () -> i8
        // CHECK:      %{{.*}} = "riscv.li"() <{"value" = 1 : i64}> : () -> !reg
        // CHECK-NEXT: %{{.*}} = "riscv.li"() <{"value" = 2 : i64}> : () -> !reg
    }) : () -> ()
}) : () -> ()
