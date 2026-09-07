// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP
//
// MLIR parses and drops `op_bundle_sizes` and `op_bundle_tags`. VeIR does
// the same.

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (!llvm.ptr, !llvm.ptr, i64)>, linkage = #llvm.linkage<external>, sym_name = "bundles"}> ({
  ^bb0(%dst: !llvm.ptr, %src: !llvm.ptr, %len: i64):
    "llvm.intr.memcpy"(%dst, %src, %len) <{isVolatile = false, op_bundle_sizes = array<i32: 1>, op_bundle_tags = ["align"]}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.intr.memmove"(%dst, %src, %len) <{isVolatile = false, op_bundle_sizes = array<i32>, op_bundle_tags = []}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "llvm.intr.memcpy"({{.*}}) <{"isVolatile" = 0 : i1}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
// CHECK: "llvm.intr.memmove"({{.*}}) <{"isVolatile" = 0 : i1}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
