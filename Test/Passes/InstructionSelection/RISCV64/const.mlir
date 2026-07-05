// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"()  <{function_type = () -> ()}> ({
    ^bb():
        %c1 = "llvm.mlir.constant"() <{"value" = -1 : i64 }> : () -> i64
        // CHECK: %[[A:.*]] = "riscv.li"() <{"value" = -1 : i64}> : () -> !riscv.reg
        // CHECK-NEXT: {{.*}} = "builtin.unrealized_conversion_cast"(%[[A]]) : (!riscv.reg) -> i64
        %c2 = "llvm.mlir.constant"() <{"value" = -1 : i32 }> : () -> i32
        // CHECK: %[[A:.*]] = "riscv.li"() <{"value" = -1 : i32}> : () -> !riscv.reg
        // CHECK-NEXT: {{.*}} = "builtin.unrealized_conversion_cast"(%[[A]]) : (!riscv.reg) -> i32
        %c3 = "llvm.mlir.constant"() <{"value" = -1 : i8 }> : () -> i8
        // CHECK: %[[A:.*]] = "riscv.li"() <{"value" = -1 : i8}> : () -> !riscv.reg
        // CHECK-NEXT: {{.*}} = "builtin.unrealized_conversion_cast"(%[[A]]) : (!riscv.reg) -> i8
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
