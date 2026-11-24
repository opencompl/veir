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

// CHECK:      illegal register allocation of function arguments: argument 0 cannot be passed in !riscv.reg<x0>, the calling convention passes it in !riscv.reg<x10>

// -----

// A virtual register is an assignment too: precolouring runs before allocation.
"builtin.module"() ({
  "riscv_cf.func"() <{sym_name = "f", function_type = (!riscv.reg<j0>) -> ()}> ({
  ^entry(%a : !riscv.reg<j0>):
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      illegal register allocation of function arguments: argument 0 cannot be passed in !riscv.reg<j0>, the calling convention passes it in !riscv.reg<x10>

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

// CHECK:      illegal register allocation of function results: result 1 cannot be returned from !riscv.reg<x10>, the copy of result 0 into it overwrites it
// CHECK-NOT:  error
