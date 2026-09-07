// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// `op_bundle_sizes` is required even when there are no bundles.
"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (i1)>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  ^bb0(%c: i1):
    "llvm.intr.assume"(%c) : (i1) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.intr.assume: missing 'op_bundle_sizes' property
