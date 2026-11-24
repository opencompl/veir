// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

// Forms of `case_values` that the verifier accepts: values at both ends of MLIR's range for the
// condition's width (from the signed minimum to the unsigned maximum), a one-element splat,
// a tensor, an empty tensor for a switch without cases, and raw little-endian hex data (MLIR's
// default spelling above 100 elements). Integer literals may also be hexadecimal, including
// negative ones. MLIR prints them as decimal, so the checks accept either spelling.
"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<i8 (i8)>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  ^bb0(%x: i8):
    "llvm.switch"(%x)[^bb1, ^bb1, ^bb1] <{case_operand_segments = array<i32: 0, 0>, case_values = dense<[-128, 255]> : vector<2xi8>, operandSegmentSizes = array<i32: 1, 0, 0>}> : (i8) -> ()
  ^bb1:
    "llvm.switch"(%x)[^bb2, ^bb2] <{case_operand_segments = array<i32: 0>, case_values = dense<7> : vector<1xi8>, operandSegmentSizes = array<i32: 1, 0, 0>}> : (i8) -> ()
  ^bb2:
    "llvm.switch"(%x)[^bb3, ^bb3, ^bb3] <{case_operand_segments = array<i32: 0, 0>, case_values = dense<[1, 2]> : tensor<2xi8>, operandSegmentSizes = array<i32: 1, 0, 0>}> : (i8) -> ()
  ^bb3:
    "llvm.switch"(%x)[^bb4] <{case_operand_segments = array<i32>, case_values = dense<> : tensor<0xi8>, operandSegmentSizes = array<i32: 1, 0, 0>}> : (i8) -> ()
  ^bb4:
    "llvm.switch"(%x)[^bb5, ^bb5, ^bb5] <{case_operand_segments = array<i32: 0, 0>, case_values = dense<"0x80FF"> : vector<2xi8>, operandSegmentSizes = array<i32: 1, 0, 0>}> : (i8) -> ()
  ^bb5:
    "llvm.switch"(%x)[^bb6, ^bb6, ^bb6] <{case_operand_segments = array<i32: 0, 0>, case_values = dense<[0xFF, - 0x80]> : vector<2xi8>, operandSegmentSizes = array<i32: 1, 0, 0>}> : (i8) -> ()
  ^bb6:
    "llvm.switch"(%x)[^bb7, ^bb7] <{case_operand_segments = array<i32: 0>, case_values = dense<0x1> : vector<1xi8>, operandSegmentSizes = array<i32: 1, 0, 0>}> : (i8) -> ()
  ^bb7:
    "llvm.return"(%x) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "case_values" = dense<[-128, {{255|-1}}]> : vector<2xi8>
// CHECK: "case_values" = dense<7> : vector<1xi8>
// CHECK: "case_values" = dense<[1, 2]> : tensor<2xi8>
// CHECK: "case_values" = dense<> : tensor<0xi8>
// CHECK: "case_values" = dense<{{"0x80FF"|\[-128, -1\]}}> : vector<2xi8>
// CHECK: "case_values" = dense<[{{0xFF|-1}}, {{- 0x80|-128}}]> : vector<2xi8>
// CHECK: "case_values" = dense<{{0x1|1}}> : vector<1xi8>
