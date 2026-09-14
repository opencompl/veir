// RUN: not veir-opt %s 2>&1 | filecheck %s --strict-whitespace
// RUN: MLIR_INVALID

"builtin.module"() ({
  "llvm.func"() <{sym_name = "bad", function_type = !llvm.func<i32 (..., ptr)>}> ({}) : () -> ()
}) : () -> ()

// CHECK:invalid-variadic.mlir:5:79: error: '...' is only valid as the last parameter of an LLVM function type
// CHECK-NEXT:  "llvm.func"() <{sym_name = "bad", function_type = !llvm.func<i32 (..., ptr)>}> ({}) : () -> ()
