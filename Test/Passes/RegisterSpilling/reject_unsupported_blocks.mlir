// RUN: not veir-opt %s --split-input-file -p=register-spilling-riscv64 2>&1 >/dev/null | filecheck %s

// Currently spilling only works on blocks with integer registers that are unallocated or preallocated to a physical register. Reject other blocks.

// reject block with `!riscv.stack` registers
"builtin.module"() ({
  "riscv_cf.func"() <{sym_name = "already_spilled", function_type = () -> ()}> ({
    %a = "riscv.li"() <{value = 5 : i64}> : () -> !riscv.reg
    %s = "riscv_regalloc.spill"(%a) : (!riscv.reg) -> !riscv.stack
    %r = "riscv_regalloc.reload"(%s) : (!riscv.stack) -> !riscv.reg
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: register spilling does not support stack registers, got !riscv.stack

// -----

// reject block with allocated virtual registers
"builtin.module"() ({
  "riscv_cf.func"() <{sym_name = "virtual", function_type = () -> ()}> ({
    %a = "riscv.li"() <{value = 5 : i64}> : () -> !riscv.reg<j0>
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: register spilling does not support virtual registers, got !riscv.reg<j0>
