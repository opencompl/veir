// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_UNREGISTERED_ROUNDTRIP

// `llvm.call` doubles as an indirect call: the callee is passed as an SSA
// operand and the `callee` symbol attribute is absent. `LLVMCallProperties`
// models `callee` as optional precisely so this round-trips with no `callee`
// attribute reintroduced.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "caller", function_type = !llvm.func<i32 (ptr, i32)>}> ({
  ^bb0(%fn: !llvm.ptr, %arg0: i32):
    %0 = "llvm.call"(%fn, %arg0) <{op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 2, 0>}> : (!llvm.ptr, i32) -> i32
    "llvm.return"(%0) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "llvm.call"(%arg{{[0-9]+_[0-9]+}}, %arg{{[0-9]+_[0-9]+}}) <{
// CHECK-NOT:    callee
// CHECK-SAME:   "op_bundle_sizes" = array<i32>
// CHECK-SAME:   "operandSegmentSizes" = array<i32: 2, 0>
// CHECK-SAME: }> : (!llvm.ptr, i32) -> i32
