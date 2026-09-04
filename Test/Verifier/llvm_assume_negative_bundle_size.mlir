// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// A bundle cannot take a negative number of operands.
"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (i1)>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  ^bb0(%c: i1):
    "llvm.intr.assume"(%c) <{op_bundle_sizes = array<i32: -1>, op_bundle_tags = ["align"]}> : (i1) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.intr.assume: op_bundle_sizes contains a negative size
