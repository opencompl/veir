// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (!llvm.ptr, i64)>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  ^bb0(%dst: !llvm.ptr, %len: i64):
    "llvm.intr.memset"(%dst, %len, %len) <{isVolatile = false}> : (!llvm.ptr, i64, i64) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.intr.memset: operand #1 must be 8-bit signless integer, but got i64
