// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// Halfword-/byte-store mirrors of `drop_zextw_sw`/`drop_sextw_sw`: `riscv.sh`
// writes only bits 15:0 and `riscv.sb` only bits 7:0 of the value operand, so a
// matching-width extension feeding that operand is redundant and gets dropped.

"builtin.module"() ({
  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> ()}> ({
  ^bb0(%addr: !riscv.reg, %val: !riscv.reg):
    %zval = "riscv.zexth"(%val) : (!riscv.reg) -> !riscv.reg
    "riscv.sh"(%addr, %zval) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
    "func.return"() : () -> ()
  }) : () -> ()

  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> ()}> ({
  ^bb0(%addr: !riscv.reg, %val: !riscv.reg):
    %sval = "riscv.sexth"(%val) : (!riscv.reg) -> !riscv.reg
    "riscv.sh"(%addr, %sval) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
    "func.return"() : () -> ()
  }) : () -> ()

  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> ()}> ({
  ^bb0(%addr: !riscv.reg, %val: !riscv.reg):
    %zval = "riscv.zextb"(%val) : (!riscv.reg) -> !riscv.reg
    "riscv.sb"(%addr, %zval) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
    "func.return"() : () -> ()
  }) : () -> ()

  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> ()}> ({
  ^bb0(%addr: !riscv.reg, %val: !riscv.reg):
    %sval = "riscv.sextb"(%val) : (!riscv.reg) -> !riscv.reg
    "riscv.sb"(%addr, %sval) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// riscv-combine alone (no dce) leaves the now-dead extension in place; what
// matters is that the store itself no longer reads through it.
// CHECK:      ^{{.*}}(%[[ZH_A:.*]] : !riscv.reg, %[[ZH_V:.*]] : !riscv.reg):
// CHECK:      "riscv.sh"(%[[ZH_A]], %[[ZH_V]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT: "func.return"() : () -> ()

// CHECK:      ^{{.*}}(%[[SH_A:.*]] : !riscv.reg, %[[SH_V:.*]] : !riscv.reg):
// CHECK:      "riscv.sh"(%[[SH_A]], %[[SH_V]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT: "func.return"() : () -> ()

// CHECK:      ^{{.*}}(%[[ZB_A:.*]] : !riscv.reg, %[[ZB_V:.*]] : !riscv.reg):
// CHECK:      "riscv.sb"(%[[ZB_A]], %[[ZB_V]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT: "func.return"() : () -> ()

// CHECK:      ^{{.*}}(%[[SB_A:.*]] : !riscv.reg, %[[SB_V:.*]] : !riscv.reg):
// CHECK:      "riscv.sb"(%[[SB_A]], %[[SB_V]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT: "func.return"() : () -> ()
