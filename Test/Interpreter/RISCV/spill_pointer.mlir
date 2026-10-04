// RUN: veir-interpret %s | filecheck %s

// Machine code spills a pointer register to the stack and reloads it. The
// stored bytes are the physical address, and casting the reloaded register
// back to a pointer finds the object again.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i64}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %v = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
    %a = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    "llvm.store"(%v, %a) : (i64, !llvm.ptr) -> ()
    %r = "builtin.unrealized_conversion_cast"(%a) : (!llvm.ptr) -> !riscv.reg
    %slot = "riscv_stack.alloca"() <{ "size" = 8 : i64, "alignment" = 8 : i64 }> : () -> !riscv.reg
    "riscv.sd"(%r, %slot) <{ "value" = 0 : i64 }> : (!riscv.reg, !riscv.reg) -> ()
    %r2 = "riscv.ld"(%slot) <{ "value" = 0 : i64 }> : (!riscv.reg) -> !riscv.reg
    %p = "builtin.unrealized_conversion_cast"(%r2) : (!riscv.reg) -> !llvm.ptr
    %out = "llvm.load"(%p) : (!llvm.ptr) -> i64
    "func.return"(%out) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000005#64]
