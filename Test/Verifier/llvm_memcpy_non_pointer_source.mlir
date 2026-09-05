// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// `llvm.intr.memcpy` reads through its second operand, so that one has to be a
// pointer too -- unlike `llvm.intr.memset`, whose second operand is the byte.
"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (!llvm.ptr, i8, i64)>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  ^bb0(%dst: !llvm.ptr, %byte: i8, %len: i64):
    "llvm.intr.memcpy"(%dst, %byte, %len) <{isVolatile = false}> : (!llvm.ptr, i8, i64) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Expected operand 1 to have !llvm.ptr type
