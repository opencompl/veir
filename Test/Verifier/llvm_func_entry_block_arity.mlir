// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "llvm.func"() <{sym_name = "f", function_type = !llvm.func<void (i32)>}> ({
  ^bb0:
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.func: entry block must have 1 arguments to match function signature
