// RUN: veir-opt %s -p=isel-br-riscv64 | filecheck %s

// As LLVM's `getOperandsForBranch`, a `g_brcond` on `x > -1` becomes `bge x, x0`, and one on
// `x < 1` becomes `bge x0, x`. Other compares against a constant compare with the constant.

"builtin.module"() ({
  "func.func"() <{sym_name = "f", function_type = (i64) -> ()}> ({
  ^bb0(%x: i64):
    %m1 = "gmir.g_constant"() <{value = -1 : i64}> : () -> i64
    %one = "gmir.g_constant"() <{value = 1 : i64}> : () -> i64
    %sgt = "gmir.g_icmp"(%x, %m1) <{predicate = 4 : i64}> : (i64, i64) -> i64
    "gmir.g_brcond"(%sgt) [^bb1, ^bb2] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i64) -> ()
  ^bb1:
    %slt = "gmir.g_icmp"(%x, %one) <{predicate = 2 : i64}> : (i64, i64) -> i64
    "gmir.g_brcond"(%slt) [^bb2, ^bb3] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i64) -> ()
  ^bb2:
    %sgt1 = "gmir.g_icmp"(%x, %one) <{predicate = 4 : i64}> : (i64, i64) -> i64
    "gmir.g_brcond"(%sgt1) [^bb3, ^bb3] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i64) -> ()
  ^bb3:
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      %[[X:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
// CHECK-NEXT: %[[X0:.*]] = "rv64.get_register"() : () -> !riscv.reg<x0>
// CHECK-NEXT: "riscv_cf.bge"(%[[X]], %[[X0]])
// CHECK:      %[[Y0:.*]] = "rv64.get_register"() : () -> !riscv.reg<x0>
// CHECK-NEXT: %[[Y:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
// CHECK-NEXT: "riscv_cf.bge"(%[[Y0]], %[[Y]])
// CHECK:      %[[ONE:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
// CHECK-NEXT: %[[Z:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
// CHECK-NEXT: "riscv_cf.blt"(%[[ONE]], %[[Z]])
