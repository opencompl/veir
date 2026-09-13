// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

// Decode at the attribute width before truncating to the result width.
// Integer attributes sign-extend, except that i1 attributes zero-extend.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i64, i64, i64, i8, i1)}> ({
    // `255 : i8` sign-extends to -1, not to 255.
    %signed = "llvm.mlir.constant"() <{value = 255 : i8}> : () -> i64
    // CHECK: %[[A:.*]] = "riscv.li"() <{"value" = -1 : i8}> : () -> !riscv.reg
    // CHECK-NEXT: {{.*}} = "builtin.unrealized_conversion_cast"(%[[A]]) : (!riscv.reg) -> i64
    // An i1 attribute is zero-extended, so `-1 : i1` in an i64 result is 1.
    %boolean = "llvm.mlir.constant"() <{value = -1 : i1}> : () -> i64
    // CHECK: %[[A:.*]] = "riscv.li"() <{"value" = 1 : i1}> : () -> !riscv.reg
    // CHECK-NEXT: {{.*}} = "builtin.unrealized_conversion_cast"(%[[A]]) : (!riscv.reg) -> i64
    // `4294967295 : i32` sign-extends to -1, not to 4294967295.
    %signed32 = "llvm.mlir.constant"() <{value = 4294967295 : i32}> : () -> i64
    // CHECK: %[[A:.*]] = "riscv.li"() <{"value" = -1 : i32}> : () -> !riscv.reg
    // CHECK-NEXT: {{.*}} = "builtin.unrealized_conversion_cast"(%[[A]]) : (!riscv.reg) -> i64
    // An attribute wider than the result carries bits that are not part of the
    // value: `300 : i32` in an i8 result is 44.
    %narrowed = "llvm.mlir.constant"() <{value = 300 : i32}> : () -> i8
    // CHECK: %[[A:.*]] = "riscv.li"() <{"value" = 44 : i32}> : () -> !riscv.reg
    // CHECK-NEXT: {{.*}} = "builtin.unrealized_conversion_cast"(%[[A]]) : (!riscv.reg) -> i8
    %true = "llvm.mlir.constant"() <{value = -1 : i1}> : () -> i1
    // CHECK: %[[A:.*]] = "riscv.li"() <{"value" = -1 : i1}> : () -> !riscv.reg
    // CHECK-NEXT: {{.*}} = "builtin.unrealized_conversion_cast"(%[[A]]) : (!riscv.reg) -> i1
    "func.return"(%signed, %boolean, %signed32, %narrowed, %true) : (i64, i64, i64, i8, i1) -> ()
  }) : () -> ()
}) : () -> ()
