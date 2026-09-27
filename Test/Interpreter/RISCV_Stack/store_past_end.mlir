// RUN: veir-interpret %s | filecheck %s

// Machine code is bounds-checked like LLVM code: a store past the end of the
// memory it allocated is UB rather than growing memory. The 8-byte alloca
// holds offsets 0..7, so the store at offset 8 is out of bounds.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (!riscv.reg)}> ({
    %v = "riscv.li"() <{ "value" = 290 : i64 }> : () -> !riscv.reg
    %p = "riscv_stack.alloca"() <{ "size" = 8 : i64, "alignment" = 8 : i64 }> : () -> !riscv.reg
    "riscv.sd"(%v, %p) <{ "value" = 8 : i64 }> : (!riscv.reg, !riscv.reg) -> ()
    "func.return"(%v) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
