// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"()  <{function_type = () -> (), sym_name = "foo"}> ({
    ^bb():
        %c1 = "llvm.mlir.constant"() <{"value" = -1 : i64 }> : () -> i64
        // CHECK: %[[A:.*]] = "riscv.li"() <{"value" = -1 : i64}> : () -> !riscv.reg
        // CHECK-NEXT: {{.*}} = "builtin.unrealized_conversion_cast"(%[[A]]) : (!riscv.reg) -> i64
        %c2 = "llvm.mlir.constant"() <{"value" = -1 : i32 }> : () -> i32
        // CHECK: %[[A:.*]] = "riscv.li"() <{"value" = -1 : i64}> : () -> !riscv.reg
        // CHECK-NEXT: {{.*}} = "builtin.unrealized_conversion_cast"(%[[A]]) : (!riscv.reg) -> i32
        %c3 = "llvm.mlir.constant"() <{"value" = -1 : i8 }> : () -> i8
        // CHECK: %[[A:.*]] = "riscv.li"() <{"value" = -1 : i64}> : () -> !riscv.reg
        // CHECK-NEXT: {{.*}} = "builtin.unrealized_conversion_cast"(%[[A]]) : (!riscv.reg) -> i8
        %c4 = "llvm.mlir.constant"() <{"value" = -1 : i1 }> : () -> i1
        // CHECK: %[[A:.*]] = "riscv.li"() <{"value" = -1 : i64}> : () -> !riscv.reg
        // CHECK-NEXT: {{.*}} = "builtin.unrealized_conversion_cast"(%[[A]]) : (!riscv.reg) -> i1
        // A positive i8 constant is sign-extended to the register width.
        %c5 = "llvm.mlir.constant"() <{"value" = 44 : i8 }> : () -> i8
        // CHECK: %[[A:.*]] = "riscv.li"() <{"value" = 44 : i64}> : () -> !riscv.reg
        // CHECK-NEXT: {{.*}} = "builtin.unrealized_conversion_cast"(%[[A]]) : (!riscv.reg) -> i8
        // A positive i64 constant keeps its value.
        %c6 = "llvm.mlir.constant"() <{"value" = 1 : i64 }> : () -> i64
        // CHECK: %[[A:.*]] = "riscv.li"() <{"value" = 1 : i64}> : () -> !riscv.reg
        // CHECK-NEXT: {{.*}} = "builtin.unrealized_conversion_cast"(%[[A]]) : (!riscv.reg) -> i64
        // Unsigned spellings of the all-ones bit pattern also denote -1.
        %c7 = "llvm.mlir.constant"() <{"value" = 18446744073709551615 : i64 }> : () -> i64
        // CHECK: %[[A:.*]] = "riscv.li"() <{"value" = -1 : i64}> : () -> !riscv.reg
        // CHECK-NEXT: {{.*}} = "builtin.unrealized_conversion_cast"(%[[A]]) : (!riscv.reg) -> i64
        // The i32 all-ones bit pattern is sign-extended into the register.
        %c8 = "llvm.mlir.constant"() <{"value" = 4294967295 : i32 }> : () -> i32
        // CHECK: %[[A:.*]] = "riscv.li"() <{"value" = -1 : i64}> : () -> !riscv.reg
        // CHECK-NEXT: {{.*}} = "builtin.unrealized_conversion_cast"(%[[A]]) : (!riscv.reg) -> i32
        "test.test"(%c1) : (i64) -> ()
        "test.test"(%c2) : (i32) -> ()
        "test.test"(%c3) : (i8) -> ()
        "test.test"(%c4) : (i1) -> ()
        "test.test"(%c5) : (i8) -> ()
        "test.test"(%c6) : (i64) -> ()
        "test.test"(%c7) : (i64) -> ()
        "test.test"(%c8) : (i32) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
