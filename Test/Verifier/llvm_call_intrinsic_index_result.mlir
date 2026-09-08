// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void ()>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
    %r = "llvm.call_intrinsic"() <{intrin = "llvm.readcyclecounter", op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 0, 0>}> : () -> index
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.call_intrinsic: result 0 must be an LLVM dialect-compatible type, but got index
