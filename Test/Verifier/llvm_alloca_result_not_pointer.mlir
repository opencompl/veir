// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (i64)>, sym_name = "f"}> ({
  ^bb0(%n: i64):
    %p = "llvm.alloca"(%n) <{alignment = 0 : i64, elem_type = i64}> : (i64) -> i64
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.alloca: Expected the result to have !llvm.ptr type
