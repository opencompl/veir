// RUN: veir-interpret %s | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s -p=riscv > %t && veir-interpret %t | filecheck %s
// RUN: filecheck %s --check-prefix=ISEL --input-file=%t

// A store and a load through a constant `getelementptr` (index 3 of an i64
// array = 24 bytes) both fold that offset into the RISC-V offset field. The
// selected code must observe the same value the LLVM-level program does, and
// no address arithmetic should survive.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    ^bb0():
      %size = "llvm.mlir.constant"() <{ "value" = 8 : i64 }> : () -> i64
      %array = "llvm.alloca"(%size) <{ "elem_type" = i64 }> : (i64) -> !llvm.ptr
      %off = "llvm.mlir.constant"() <{ "value" = 3 : i64 }> : () -> i64
      %val = "llvm.mlir.constant"() <{ "value" = 170 : i64 }> : () -> i64
      %p1 = "llvm.getelementptr"(%array, %off) <{ elem_type = i64, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
      "llvm.store"(%val, %p1) : (i64, !llvm.ptr) -> ()
      %p2 = "llvm.getelementptr"(%array, %off) <{ elem_type = i64, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
      %out = "llvm.load"(%p2) : (!llvm.ptr) -> i64
      "llvm.return"(%out) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// SRC: Program output: #[0x00000000000000aa#64]
// CHECK: Program output: #[0x00000000000000aa#64]

// The `sh3add` that would have scaled the index is gone: both accesses address
// the alloca directly at offset 24.
// ISEL-NOT: riscv.sh3add
// ISEL:     "riscv.sd"({{.*}}, {{.*}}) <{"value" = 24 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// ISEL:     {{.*}} = "riscv.ld"({{.*}}) <{"value" = 24 : i64}> : (!riscv.reg) -> !riscv.reg
