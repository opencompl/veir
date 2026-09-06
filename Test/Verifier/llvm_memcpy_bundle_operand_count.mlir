// RUN: not veir-opt %s 2>&1 | filecheck %s

// A memory intrinsic takes three operands, so a bundle asking for a fourth is
// rejected. `mlir-opt` parses `op_bundle_sizes` and throws it away instead, so
// there is no MLIR run line.
"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (!llvm.ptr, !llvm.ptr, i64)>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  ^bb0(%dst: !llvm.ptr, %src: !llvm.ptr, %len: i64):
    "llvm.intr.memcpy"(%dst, %src, %len) <{isVolatile = false, op_bundle_sizes = array<i32: 1>, op_bundle_tags = ["align"]}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.intr.memcpy: Expected 'op_bundle_sizes' to be all zero
