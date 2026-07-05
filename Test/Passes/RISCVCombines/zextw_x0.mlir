// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `riscv.zextw` of the hard-wired zero register `x0` is a no-op: `x0` always
// reads as 0, so it already has bits 63:32 clear.

"builtin.module"() ({
  "func.func"() <{function_type = () -> !riscv.reg}> ({
  ^bb0():
    %x0 = "rv64.get_register"() : () -> !riscv.reg<x0>
    %z = "riscv.zextw"(%x0) : (!riscv.reg<x0>) -> !riscv.reg
    "func.return"(%z) : (!riscv.reg) -> ()
  }) : () -> ()

  // Negative case: a plain (non-`x0`-typed) register must be left alone.
  "func.func"() <{function_type = (!riscv.reg) -> !riscv.reg}> ({
  ^bb0(%x: !riscv.reg):
    %z = "riscv.zextw"(%x) : (!riscv.reg) -> !riscv.reg
    "func.return"(%z) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      %[[X0:.*]] = "rv64.get_register"() : () -> !riscv.reg<x0>
// CHECK-NEXT: "func.return"(%[[X0]]) : (!riscv.reg<x0>) -> ()

// CHECK:      %[[X:.*]] = "riscv.zextw"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: "func.return"(%[[X]]) : (!riscv.reg) -> ()
