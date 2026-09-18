// RUN: veir-interpret %s | filecheck %s

// Machine code may run past the end of an object into the gap before the
// next one: the object grows to cover the access. The 8-byte store at offset
// 8 of the first 8-byte alloca lands in the gap, and the load reads it back.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (!riscv.reg)}> ({
    %v = "riscv.li"() <{ "value" = 290 : i64 }> : () -> !riscv.reg
    %p = "riscv_stack.alloca"() <{ "size" = 8 : i64, "alignment" = 8 : i64 }> : () -> !riscv.reg
    %q = "riscv_stack.alloca"() <{ "size" = 8 : i64, "alignment" = 8 : i64 }> : () -> !riscv.reg
    "riscv.sd"(%v, %p) <{ "value" = 8 : i64 }> : (!riscv.reg, !riscv.reg) -> ()
    %r = "riscv.ld"(%p) <{ "value" = 8 : i64 }> : (!riscv.reg) -> !riscv.reg
    "func.return"(%r) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000122#64]
