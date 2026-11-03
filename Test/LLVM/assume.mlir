// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP
//
// `llvm.intr.assume` takes an `i1` condition followed by the operands of its
// operand bundles: `op_bundle_sizes` gives the operand count of each bundle
// and `op_bundle_tags` its name, and is omitted when there are no bundles.
// LLVM only allows bundles on a constant `true` condition.

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (i1, !llvm.ptr)>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  ^bb0(%c: i1, %p: !llvm.ptr):
    %true = "llvm.mlir.constant"() <{value = 1 : i1}> : () -> i1
    %four = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    "llvm.intr.assume"(%c) <{op_bundle_sizes = array<i32>}> : (i1) -> ()
    "llvm.intr.assume"(%true, %p, %four) <{op_bundle_sizes = array<i32: 2>, op_bundle_tags = ["align"]}> : (i1, !llvm.ptr, i64) -> ()
    "llvm.intr.assume"(%true, %p, %four, %p) <{op_bundle_sizes = array<i32: 2, 1>, op_bundle_tags = ["align", "nonnull"]}> : (i1, !llvm.ptr, i64, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "llvm.intr.assume"(%{{.*}}) <{"op_bundle_sizes" = array<i32>}> : (i1) -> ()
// CHECK-NEXT: "llvm.intr.assume"(%{{.*}}, %{{.*}}, %{{.*}}) <{"op_bundle_sizes" = array<i32: 2>, "op_bundle_tags" = ["align"]}> : (i1, !llvm.ptr, i64) -> ()
// CHECK-NEXT: "llvm.intr.assume"(%{{.*}}, %{{.*}}, %{{.*}}, %{{.*}}) <{"op_bundle_sizes" = array<i32: 2, 1>, "op_bundle_tags" = ["align", "nonnull"]}> : (i1, !llvm.ptr, i64, !llvm.ptr) -> ()
