// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// Halfword-/byte-store mirrors of `drop_zextw_sw`/`drop_sextw_sw`: `riscv.sh`
// writes only bits 15:0 and `riscv.sb` only bits 7:0 of the value operand, so a
// matching-width extension feeding that operand is redundant and gets dropped.
//
// The store's operand order is *value first, address second* (the isel and
// interpreter convention): `"riscv.sh"(%value, %address)`. Only the value
// operand (index 0) is stripped; the address operand (index 1) is left untouched.

"builtin.module"() ({
  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> ()}> ({
  ^bb0(%val: !riscv.reg, %addr: !riscv.reg):
    %zval = "riscv.zexth"(%val) : (!riscv.reg) -> !riscv.reg
    "riscv.sh"(%zval, %addr) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
    "func.return"() : () -> ()
  }) : () -> ()

  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> ()}> ({
  ^bb0(%val: !riscv.reg, %addr: !riscv.reg):
    %sval = "riscv.sexth"(%val) : (!riscv.reg) -> !riscv.reg
    "riscv.sh"(%sval, %addr) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
    "func.return"() : () -> ()
  }) : () -> ()

  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> ()}> ({
  ^bb0(%val: !riscv.reg, %addr: !riscv.reg):
    %zval = "riscv.zextb"(%val) : (!riscv.reg) -> !riscv.reg
    "riscv.sb"(%zval, %addr) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
    "func.return"() : () -> ()
  }) : () -> ()

  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> ()}> ({
  ^bb0(%val: !riscv.reg, %addr: !riscv.reg):
    %sval = "riscv.sextb"(%val) : (!riscv.reg) -> !riscv.reg
    "riscv.sb"(%sval, %addr) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// riscv-combine alone (no dce) leaves the now-dead extension in place; what
// matters is that the store itself no longer reads through it.
// CHECK:      ^{{.*}}(%[[ZH_V:.*]] : !riscv.reg, %[[ZH_A:.*]] : !riscv.reg):
// CHECK:      "riscv.sh"(%[[ZH_V]], %[[ZH_A]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT: "func.return"() : () -> ()

// CHECK:      ^{{.*}}(%[[SH_V:.*]] : !riscv.reg, %[[SH_A:.*]] : !riscv.reg):
// CHECK:      "riscv.sh"(%[[SH_V]], %[[SH_A]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT: "func.return"() : () -> ()

// CHECK:      ^{{.*}}(%[[ZB_V:.*]] : !riscv.reg, %[[ZB_A:.*]] : !riscv.reg):
// CHECK:      "riscv.sb"(%[[ZB_V]], %[[ZB_A]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT: "func.return"() : () -> ()

// CHECK:      ^{{.*}}(%[[SB_V:.*]] : !riscv.reg, %[[SB_A:.*]] : !riscv.reg):
// CHECK:      "riscv.sb"(%[[SB_V]], %[[SB_A]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT: "func.return"() : () -> ()
