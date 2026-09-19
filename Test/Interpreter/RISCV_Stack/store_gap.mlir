// RUN: veir-interpret %s | filecheck %s

// Machine code is bounds-checked like LLVM code: an access past the end of
// an object is UB even where the gap before the next object would have room.
// The 8-byte store at offset 8 of the first 8-byte alloca lands in the gap.

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

// CHECK: Undefined behavior
