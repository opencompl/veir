// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

// MLIR prints `i1` dense elements as `true` and `false`; the verifier reads them as 1 and 0.
"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<i1 (i1)>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  ^bb0(%x: i1):
    "llvm.switch"(%x)[^bb1, ^bb1] <{case_operand_segments = array<i32: 0>, case_values = dense<true> : vector<1xi1>, operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb1:
    "llvm.switch"(%x)[^bb2, ^bb2, ^bb2] <{case_operand_segments = array<i32: 0, 0>, case_values = dense<[false, true]> : vector<2xi1>, operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb2:
    "llvm.return"(%x) : (i1) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "case_values" = dense<true> : vector<1xi1>
// CHECK: "case_values" = dense<[false, true]> : vector<2xi1>
