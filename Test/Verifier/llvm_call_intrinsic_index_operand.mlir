// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "func.func"() <{function_type = (index) -> (), sym_name = "f"}> ({
  ^bb0(%i: index):
    "llvm.call_intrinsic"(%i) <{intrin = "llvm.assume", op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>}> : (index) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.call_intrinsic: operand 0 must be an LLVM dialect-compatible type, but got index
