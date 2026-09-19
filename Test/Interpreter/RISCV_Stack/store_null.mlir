// RUN: veir-interpret %s | filecheck %s

// The null object at address 0 holds no bytes, so a machine store through a
// zero register is UB, as a null dereference is in LLVM code.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (!riscv.reg)}> ({
    %v = "riscv.li"() <{ "value" = 290 : i64 }> : () -> !riscv.reg
    %p = "riscv.li"() <{ "value" = 0 : i64 }> : () -> !riscv.reg
    "riscv.sd"(%v, %p) <{ "value" = 0 : i64 }> : (!riscv.reg, !riscv.reg) -> ()
    "func.return"(%v) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
