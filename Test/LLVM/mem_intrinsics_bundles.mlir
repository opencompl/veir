// RUN: VEIR_ROUNDTRIP
//
// `op_bundle_sizes` and `op_bundle_tags` are parsed on the memory intrinsics
// and kept. There is no MLIR run line because `mlir-opt` does not keep them:
// it parses both and then discards them, holding the operand count at three,
// so an operand bundle has nowhere to put its operands. VeIR preserves what it
// was given rather than dropping it silently -- but refuses a bundle size that
// would ask for a fourth operand, which is the check in
// Test/Verifier/llvm_memcpy_bundle_operand_count.mlir.

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (!llvm.ptr, !llvm.ptr, i64)>, linkage = #llvm.linkage<external>, sym_name = "bundles"}> ({
  ^bb0(%dst: !llvm.ptr, %src: !llvm.ptr, %len: i64):
    "llvm.intr.memcpy"(%dst, %src, %len) <{isVolatile = false, op_bundle_sizes = array<i32>, op_bundle_tags = []}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    // A bundle that asks for no operands is the only kind that fits.
    "llvm.intr.memmove"(%dst, %src, %len) <{isVolatile = false, op_bundle_sizes = array<i32: 0>, op_bundle_tags = ["align"]}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "llvm.intr.memcpy"({{.*}}) <{"isVolatile" = 0 : i1, "op_bundle_sizes" = array<i32>, "op_bundle_tags" = []}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
// CHECK: "llvm.intr.memmove"({{.*}}) <{"isVolatile" = 0 : i1, "op_bundle_sizes" = array<i32: 0>, "op_bundle_tags" = ["align"]}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
