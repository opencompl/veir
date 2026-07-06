// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// Byte- and half-word mirrors of `zextw_zextw`/`sextw_sextw`: each extension is
// idempotent, so the redundant outer one is dropped.

"builtin.module"() ({
  "func.func"() <{function_type = (!riscv.reg) -> !riscv.reg}> ({
  ^bb0(%x: !riscv.reg):
    %i = "riscv.zextb"(%x) : (!riscv.reg) -> !riscv.reg
    %o = "riscv.zextb"(%i) : (!riscv.reg) -> !riscv.reg
    "func.return"(%o) : (!riscv.reg) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (!riscv.reg) -> !riscv.reg}> ({
  ^bb0(%x: !riscv.reg):
    %i = "riscv.zexth"(%x) : (!riscv.reg) -> !riscv.reg
    %o = "riscv.zexth"(%i) : (!riscv.reg) -> !riscv.reg
    "func.return"(%o) : (!riscv.reg) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (!riscv.reg) -> !riscv.reg}> ({
  ^bb0(%x: !riscv.reg):
    %i = "riscv.sextb"(%x) : (!riscv.reg) -> !riscv.reg
    %o = "riscv.sextb"(%i) : (!riscv.reg) -> !riscv.reg
    "func.return"(%o) : (!riscv.reg) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (!riscv.reg) -> !riscv.reg}> ({
  ^bb0(%x: !riscv.reg):
    %i = "riscv.sexth"(%x) : (!riscv.reg) -> !riscv.reg
    %o = "riscv.sexth"(%i) : (!riscv.reg) -> !riscv.reg
    "func.return"(%o) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      ^{{.*}}(%[[ZB_X:.*]] : !riscv.reg):
// CHECK-NEXT: %[[ZB_I:.*]] = "riscv.zextb"(%[[ZB_X]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: "func.return"(%[[ZB_I]]) : (!riscv.reg) -> ()

// CHECK:      ^{{.*}}(%[[ZH_X:.*]] : !riscv.reg):
// CHECK-NEXT: %[[ZH_I:.*]] = "riscv.zexth"(%[[ZH_X]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: "func.return"(%[[ZH_I]]) : (!riscv.reg) -> ()

// CHECK:      ^{{.*}}(%[[SB_X:.*]] : !riscv.reg):
// CHECK-NEXT: %[[SB_I:.*]] = "riscv.sextb"(%[[SB_X]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: "func.return"(%[[SB_I]]) : (!riscv.reg) -> ()

// CHECK:      ^{{.*}}(%[[SH_X:.*]] : !riscv.reg):
// CHECK-NEXT: %[[SH_I:.*]] = "riscv.sexth"(%[[SH_X]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: "func.return"(%[[SH_I]]) : (!riscv.reg) -> ()
