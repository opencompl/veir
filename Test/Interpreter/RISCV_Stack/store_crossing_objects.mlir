// RUN: veir-interpret %s | filecheck %s

// An object can only grow up to the start of the next one. The second
// 8-byte alloca starts 16 bytes after the first, so an 8-byte store at
// offset 12 of the first would reach into the second and is UB.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (!riscv.reg)}> ({
    %v = "riscv.li"() <{ "value" = 290 : i64 }> : () -> !riscv.reg
    %p = "riscv_stack.alloca"() <{ "size" = 8 : i64, "alignment" = 8 : i64 }> : () -> !riscv.reg
    %q = "riscv_stack.alloca"() <{ "size" = 8 : i64, "alignment" = 8 : i64 }> : () -> !riscv.reg
    "riscv.sd"(%v, %p) <{ "value" = 12 : i64 }> : (!riscv.reg, !riscv.reg) -> ()
    %r = "riscv.ld"(%q) <{ "value" = 0 : i64 }> : (!riscv.reg) -> !riscv.reg
    "func.return"(%r) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
