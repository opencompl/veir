// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<i64 (!llvm.ptr, i1)>, linkage = #llvm.linkage<external>, sym_name = "sizes"}> ({
  ^bb0(%p: !llvm.ptr, %b: i1):
    // The shape clang emits: four arguments, no bundles.
    %r = "llvm.call_intrinsic"(%p, %b, %b, %b) <{fastmathFlags = #llvm.fastmath<none>, intrin = "llvm.objectsize.i64.p0", op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 4, 0>}> : (!llvm.ptr, i1, i1, i1) -> i64
    // No arguments and no result at all.
    "llvm.call_intrinsic"() <{intrin = "llvm.donothing", op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 0, 0>}> : () -> ()
    // One bundle, whose single operand follows the argument.
    "llvm.call_intrinsic"(%p, %b) <{intrin = "llvm.assume", op_bundle_sizes = array<i32: 1>, op_bundle_tags = ["align"], operandSegmentSizes = array<i32: 1, 1>}> : (!llvm.ptr, i1) -> ()
    "llvm.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "llvm.call_intrinsic"({{.*}}) <{"fastmathFlags" = #llvm.fastmath<none>, "intrin" = "llvm.objectsize.i64.p0", "op_bundle_sizes" = array<i32>, "operandSegmentSizes" = array<i32: 4, 0>}> : (!llvm.ptr, i1, i1, i1) -> i64
// CHECK: "llvm.call_intrinsic"() <{"fastmathFlags" = #llvm.fastmath<none>, "intrin" = "llvm.donothing", "op_bundle_sizes" = array<i32>, "operandSegmentSizes" = array<i32: 0, 0>}> : () -> ()
// CHECK: "llvm.call_intrinsic"({{.*}}) <{"fastmathFlags" = #llvm.fastmath<none>, "intrin" = "llvm.assume", "op_bundle_sizes" = array<i32: 1>, "op_bundle_tags" = ["align"], "operandSegmentSizes" = array<i32: 1, 1>}> : (!llvm.ptr, i1) -> ()
