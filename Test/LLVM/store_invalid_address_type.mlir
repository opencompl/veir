// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (i32, i64)>, sym_name = "f"}> ({
  ^bb0(%value: i32, %address: i64):
    "llvm.store"(%value, %address) : (i32, i64) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.store: Expected operand 1 to have !llvm.ptr type
