// RUN: not veir-opt %s --split-input-file -p=register-precolouring-riscv64 2>&1 >/dev/null | filecheck %s

// Precolouring accepts the same function shapes as register allocation (see `unsupported-functions.mlir`).
// These cases cover values that are pre-assigned to a register the calling convention cannot accommodate.

// Argument 0 belongs in a0 (x10), not in x0.
"builtin.module"() ({
  "riscv_cf.func"() <{sym_name = "f", function_type = (!riscv.reg<x0>) -> ()}> ({
  ^entry(%a : !riscv.reg<x0>):
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// -----

// A virtual register is an assignment too: precolouring runs before allocation.
"builtin.module"() ({
  "riscv_cf.func"() <{sym_name = "f", function_type = (!riscv.reg<j0>) -> ()}> ({
  ^entry(%a : !riscv.reg<j0>):
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// -----

// The result copies run one after another: copying %b into a0 would clobber %a, which is
// already in a0 and still has to be copied into a1.
"builtin.module"() ({
  "riscv_cf.func"() <{sym_name = "f", function_type = () -> (!riscv.reg, !riscv.reg)}> ({
    %a = "riscv.li"() <{value = 5 : i64}> : () -> !riscv.reg<x10>
    %b = "riscv.li"() <{value = 7 : i64}> : () -> !riscv.reg
    "riscv_cf.return"(%b, %a) : (!riscv.reg, !riscv.reg<x10>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      precolouring cannot move argument 0 of type !riscv.reg<x0> into !riscv.reg<x10>
// CHECK:      precolouring cannot move argument 0 of type !riscv.reg<j0> into !riscv.reg<x10>
// CHECK:      precolouring cannot return result 1 from a0: the copy of result 0 into a0 overwrites it
// CHECK-NOT:  error
