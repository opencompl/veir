// RUN: veir-interpret %s | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s -p=riscv > %t && veir-interpret %t | filecheck %s
// RUN: filecheck %s --check-prefix=ISEL --input-file=%t

// Two stack slots, written and read back through separate pointers. The
// selected code must observe the same values the LLVM-level program does, which
// requires the two `riscv_stack.alloca`s to name distinct memory.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    ^bb0():
      %c1 = "llvm.mlir.constant"() <{ "value" = 1 : i64 }> : () -> i64
      %lhs = "llvm.mlir.constant"() <{ "value" = 100 : i64 }> : () -> i64
      %rhs = "llvm.mlir.constant"() <{ "value" = 7 : i64 }> : () -> i64
      %p = "llvm.alloca"(%c1) <{ elem_type = i64 }> : (i64) -> !llvm.ptr
      %q = "llvm.alloca"(%c1) <{ elem_type = i64 }> : (i64) -> !llvm.ptr
      "llvm.store"(%lhs, %p) : (i64, !llvm.ptr) -> ()
      "llvm.store"(%rhs, %q) : (i64, !llvm.ptr) -> ()
      %a = "llvm.load"(%p) : (!llvm.ptr) -> i64
      %b = "llvm.load"(%q) : (!llvm.ptr) -> i64
      %out = "llvm.sub"(%a, %b) : (i64, i64) -> i64
      "llvm.return"(%out) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// SRC: Program output: #[0x000000000000005d#64]
// CHECK: Program output: #[0x000000000000005d#64]

// Both allocas become stack objects, and no LLVM-level memory op survives.
// ISEL:     "riscv_stack.alloca"() <{"alignment" = 8 : i64, "size" = 8 : i64}> : () -> !riscv.reg
// ISEL:     "riscv_stack.alloca"() <{"alignment" = 8 : i64, "size" = 8 : i64}> : () -> !riscv.reg
// ISEL-NOT: llvm.alloca
// ISEL-NOT: llvm.store
// ISEL-NOT: llvm.load
