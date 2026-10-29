// RUN: veir-opt %s -p=isel-br-riscv64 | filecheck %s

// A `g_icmp` is fused with the `g_brcond` on its result only when it comes right
// before the branch. Otherwise the branch tests the condition with `bnez`.

"builtin.module"() ({
  "func.func"() <{sym_name = "f", function_type = (i64, i64) -> ()}> ({
  ^bb0(%x: i64, %y: i64):
    %c = "gmir.g_icmp"(%x, %y) <{predicate = 2 : i64}> : (i64, i64) -> i64
    %z = "gmir.g_add"(%x, %y) : (i64, i64) -> i64
    "gmir.g_brcond"(%c) [^bb1, ^bb2] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i64) -> ()
  ^bb1:
    %d = "gmir.g_icmp"(%x, %y) <{predicate = 2 : i64}> : (i64, i64) -> i64
    "gmir.g_brcond"(%d) [^bb2, ^bb2] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i64) -> ()
  ^bb2:
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      %[[C:.*]] = "gmir.g_icmp"
// CHECK-NEXT: "gmir.g_add"
// CHECK-NEXT: %[[R:.*]] = "builtin.unrealized_conversion_cast"(%[[C]]) : (i64) -> !riscv.reg
// CHECK-NEXT: "riscv_cf.bnez"(%[[R]])
// CHECK:      "gmir.g_icmp"
// CHECK-NEXT: "builtin.unrealized_conversion_cast"
// CHECK-NEXT: "builtin.unrealized_conversion_cast"
// CHECK-NEXT: "riscv_cf.blt"
