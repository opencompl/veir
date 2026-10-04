// REQUIRES: llubi
// RUN: not %llubi-interpret %s 2>&1 | filecheck %s

// A negative test of the translator: an operation it does not support must
// fail the cross-check loudly instead of passing it silently.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %p = "llvm.mlir.zero"() : () -> !llvm.ptr
    %i = "llvm.ptrtoint"(%p) : (!llvm.ptr) -> i64
    "llvm.return"(%i) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: veir2llvm: error: unsupported LLVM operation: llvm.ptrtoint
