// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// Byte- and half-word mirrors of `zextw_x0`/`sextw_x0`: any extension of the
// hard-wired zero register `x0` (which reads as 0) is a no-op.

"builtin.module"() ({
  "func.func"() <{function_type = () -> !riscv.reg, sym_name = "f0"}> ({
  ^bb0():
    %x0 = "rv64.get_register"() : () -> !riscv.reg<x0>
    %z = "riscv.zextb"(%x0) : (!riscv.reg<x0>) -> !riscv.reg
    "func.return"(%z) : (!riscv.reg) -> ()
  }) : () -> ()

  "func.func"() <{function_type = () -> !riscv.reg, sym_name = "f1"}> ({
  ^bb0():
    %x0 = "rv64.get_register"() : () -> !riscv.reg<x0>
    %z = "riscv.zexth"(%x0) : (!riscv.reg<x0>) -> !riscv.reg
    "func.return"(%z) : (!riscv.reg) -> ()
  }) : () -> ()

  "func.func"() <{function_type = () -> !riscv.reg, sym_name = "f2"}> ({
  ^bb0():
    %x0 = "rv64.get_register"() : () -> !riscv.reg<x0>
    %z = "riscv.sextb"(%x0) : (!riscv.reg<x0>) -> !riscv.reg
    "func.return"(%z) : (!riscv.reg) -> ()
  }) : () -> ()

  "func.func"() <{function_type = () -> !riscv.reg, sym_name = "f3"}> ({
  ^bb0():
    %x0 = "rv64.get_register"() : () -> !riscv.reg<x0>
    %z = "riscv.sexth"(%x0) : (!riscv.reg<x0>) -> !riscv.reg
    "func.return"(%z) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      %[[ZB0:.*]] = "rv64.get_register"() : () -> !riscv.reg<x0>
// CHECK-NEXT: "func.return"(%[[ZB0]]) : (!riscv.reg<x0>) -> ()

// CHECK:      %[[ZH0:.*]] = "rv64.get_register"() : () -> !riscv.reg<x0>
// CHECK-NEXT: "func.return"(%[[ZH0]]) : (!riscv.reg<x0>) -> ()

// CHECK:      %[[SB0:.*]] = "rv64.get_register"() : () -> !riscv.reg<x0>
// CHECK-NEXT: "func.return"(%[[SB0]]) : (!riscv.reg<x0>) -> ()

// CHECK:      %[[SH0:.*]] = "rv64.get_register"() : () -> !riscv.reg<x0>
// CHECK-NEXT: "func.return"(%[[SH0]]) : (!riscv.reg<x0>) -> ()
