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
        // An unsigned spelling is normalized by the parser: `255 : i8` is -1.
        %c7 = "llvm.mlir.constant"() <{"value" = 255 : i8 }> : () -> i8
        // CHECK: %[[A:.*]] = "riscv.li"() <{"value" = -1 : i64}> : () -> !riscv.reg
        // CHECK-NEXT: {{.*}} = "builtin.unrealized_conversion_cast"(%[[A]]) : (!riscv.reg) -> i8
        // Likewise `4294967295 : i32` is -1.
        %c8 = "llvm.mlir.constant"() <{"value" = 4294967295 : i32 }> : () -> i32
        // CHECK: %[[A:.*]] = "riscv.li"() <{"value" = -1 : i64}> : () -> !riscv.reg
        // CHECK-NEXT: {{.*}} = "builtin.unrealized_conversion_cast"(%[[A]]) : (!riscv.reg) -> i32
        // Every width up to 64 is lowered, including non-power-of-two widths.
        %c9 = "llvm.mlir.constant"() <{"value" = 32767 : i16 }> : () -> i16
        // CHECK: %[[A:.*]] = "riscv.li"() <{"value" = 32767 : i64}> : () -> !riscv.reg
        // CHECK-NEXT: {{.*}} = "builtin.unrealized_conversion_cast"(%[[A]]) : (!riscv.reg) -> i16
        %c10 = "llvm.mlir.constant"() <{"value" = -3 : i3 }> : () -> i3
        // CHECK: %[[A:.*]] = "riscv.li"() <{"value" = -3 : i64}> : () -> !riscv.reg
        // CHECK-NEXT: {{.*}} = "builtin.unrealized_conversion_cast"(%[[A]]) : (!riscv.reg) -> i3
        %c11 = "llvm.mlir.constant"() <{"value" = -2251799813685248 : i52 }> : () -> i52
        // CHECK: %[[A:.*]] = "riscv.li"() <{"value" = -2251799813685248 : i64}> : () -> !riscv.reg
        // CHECK-NEXT: {{.*}} = "builtin.unrealized_conversion_cast"(%[[A]]) : (!riscv.reg) -> i52
        // Wider than a register: not lowered.
        %c12 = "llvm.mlir.constant"() <{"value" = -1 : i65 }> : () -> i65
        // CHECK: {{.*}} = "llvm.mlir.constant"() <{"value" = -1 : i65}> : () -> i65
        "test.test"(%c1) : (i64) -> ()
        "test.test"(%c2) : (i32) -> ()
        "test.test"(%c3) : (i8) -> ()
        "test.test"(%c4) : (i1) -> ()
        "test.test"(%c7) : (i8) -> ()
        "test.test"(%c8) : (i32) -> ()
        "test.test"(%c9) : (i16) -> ()
        "test.test"(%c10) : (i3) -> ()
        "test.test"(%c11) : (i52) -> ()
        "test.test"(%c12) : (i65) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
