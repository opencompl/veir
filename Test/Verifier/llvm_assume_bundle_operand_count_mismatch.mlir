// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// Every operand after the condition belongs to a bundle, so an extra pointer
// with no bundle to hold it is an error.
"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (i1, !llvm.ptr)>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  ^bb0(%c: i1, %p: !llvm.ptr):
    "llvm.intr.assume"(%c, %p) <{op_bundle_sizes = array<i32>}> : (i1, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.intr.assume: Expected 1 condition and 0 operand bundle operand(s) per 'op_bundle_sizes', but got 2 operand(s)
