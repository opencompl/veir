// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"() ({
        %one = "llvm.mlir.constant"() <{ "value" = 1 : i64 }> : () -> i64
        %two = "llvm.mlir.constant"() <{ "value" = 2 : i64 }> : () -> i64
        // CHECK: [[A:%.*]] = "riscv.li"() <{"value" = 1 : i64}> : () -> !reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"([[A]]) : (!reg) -> i64
        // CHECK-NEXT: [[B:%.*]] = "riscv.li"() <{"value" = 2 : i64}> : () -> !reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"([[B]]) : (!reg) -> i64
    }) : () -> ()
}) : () -> ()
