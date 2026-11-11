// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (i64)>, sym_name = "f"}> ({
  ^bb0(%address: i64):
    %value = "llvm.load"(%address) : (i64) -> i32
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.load: Expected operand 0 to have !llvm.ptr type
