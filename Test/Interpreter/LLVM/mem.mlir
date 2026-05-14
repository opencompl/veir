// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %1 = "llvm.mlir.constant"() <{ "value" = 1 : i64 }> : () -> i64
  %2 = "llvm.mlir.constant"() <{ "value" = 8 : i64 }> : () -> i64
  %3 = "llvm.alloca"(%1) <{ "elem_type" = i64 }> : (i64) -> !llvm.ptr
  "llvm.store"(%3, %2) : (!llvm.ptr, i64) -> ()
  %4 = "llvm.load"(%3) : (!llvm.ptr) -> i64
  "func.return"(%4) : (i64) -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000008#64]
