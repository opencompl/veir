// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP
//
// `#llvm.constant_range<iN, lo, hi>` is the half-open range a value is known
// to lie in. It reaches VeIR as `llvm.range` inside the `arg_attrs` and
// `res_attrs` dictionaries of `llvm.func` and `llvm.call`. The body is kept
// verbatim, so the case that matters is the wrapping range: LLVM allows
// `hi < lo`, and the bound prints back negative.

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<i32 (i32)>, linkage = #llvm.linkage<external>, sym_name = "callee", arg_attrs = [{llvm.noundef, llvm.range = #llvm.constant_range<i32, 0, 20>}], res_attrs = [{llvm.noundef, llvm.range = #llvm.constant_range<i32, 0, 19>}]}> ({
  ^bb0(%x: i32):
    "llvm.return"(%x) : (i32) -> ()
  }) : () -> ()
  // A range that wraps: the upper bound reads as negative.
  "llvm.func"() <{function_type = !llvm.func<i64 ()>, linkage = #llvm.linkage<external>, sym_name = "wrapping", res_attrs = [{llvm.range = #llvm.constant_range<i32, 0, -7>}]}> ({
    %c = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    "llvm.return"(%c) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "llvm.range" = #llvm.constant_range<i32, 0, 20>
// CHECK: "llvm.range" = #llvm.constant_range<i32, 0, 19>
// CHECK: "llvm.range" = #llvm.constant_range<i32, 0, -7>
