// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// The condition of `llvm.intr.assume` is a single bit; an i32 is not one.
"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (i32)>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  ^bb0(%x: i32):
    "llvm.intr.assume"(%x) <{op_bundle_sizes = array<i32>}> : (i32) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.intr.assume: Expected i1 condition
