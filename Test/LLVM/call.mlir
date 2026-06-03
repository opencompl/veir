// RUN: VEIR_ROUNDTRIP

"builtin.module"() ({
  "llvm.func"() <{sym_name = "callee", function_type = !llvm.func<i32 (i32)>}> ({
  ^bb0(%arg0: i32):
    "llvm.return"(%arg0) : (i32) -> ()
  }) : () -> ()
  "llvm.func"() <{sym_name = "caller", function_type = !llvm.func<i32 (i32)>}> ({
  ^bb0(%arg0: i32):
    %0 = "llvm.call"(%arg0) <{callee = @callee, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>}> : (i32) -> i32
    "llvm.return"(%0) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// The explicitly-modelled `callee` and the preserved `extra` attributes must
// all survive the round-trip.
// CHECK:      "llvm.call"(%arg{{[0-9]+_[0-9]+}}) <{
// CHECK-SAME:   "callee" = @callee
// CHECK-SAME:   "op_bundle_sizes" = array<i32>
// CHECK-SAME:   "operandSegmentSizes" = array<i32: 1, 0>
// CHECK-SAME: }> : (i32) -> i32
