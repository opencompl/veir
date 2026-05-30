// RUN: not veir-opt %s 2>&1 | filecheck %s --strict-whitespace

"builtin.module"() ({
  "llvm.func"() <{sym_name = "bad", function_type = !llvm.func<i32 (..., ptr)>}> ({}) : () -> ()
}) : () -> ()

// CHECK:invalid-variadic.mlir:4:79: error: '...' is only valid as the last parameter of an LLVM function type
// CHECK-NEXT:  "llvm.func"() <{sym_name = "bad", function_type = !llvm.func<i32 (..., ptr)>}> ({}) : () -> ()
