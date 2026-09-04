// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// `op_bundle_sizes` is an i32 dense array in MLIR; other element types are
// rejected rather than widened.
"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (i1)>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  ^bb0(%c: i1):
    "llvm.intr.assume"(%c) <{op_bundle_sizes = array<i64>}> : (i1) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.intr.assume: Expected 'op_bundle_sizes' to be an i32 dense array attribute
