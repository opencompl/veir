// REQUIRES: llubi
// RUN: not %llubi-interpret %s 2>&1 | filecheck %s

// A negative test of the translator: an operation it does not support must
// fail the cross-check loudly instead of passing it silently.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %z = "llvm.mlir.zero"() : () -> i64
    "llvm.return"(%z) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: veir2llvm: error: unsupported LLVM operation: llvm.mlir.zero
