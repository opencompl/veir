// RUN: veir-interpret %s | filecheck %s

// An 8-byte store at offset 4 of an 8-byte alloca begins in bounds and runs
// past the end, so it is UB.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> ()}> ({
    %v = "riscv.li"() <{ "value" = 42 : i64 }> : () -> !riscv.reg
    %p = "riscv_stack.alloca"() <{ "size" = 8 : i64, "alignment" = 8 : i64 }> : () -> !riscv.reg
    "riscv.sd"(%v, %p) <{ "value" = 4 : i64 }> : (!riscv.reg, !riscv.reg) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
