// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP
//
// `llvm.switch` is a terminator with one default destination and one
// destination per case. `operandSegmentSizes` splits its operands into the
// value, the default destination's operands and all case operands;
// `case_operand_segments` splits that last group one entry per case. The
// optional `case_values` and `branch_weights` are omitted when absent.

"builtin.module"() ({
  // No cases at all: the value is read, and control always reaches the default.
  "llvm.func"() <{function_type = !llvm.func<i32 (i32)>, linkage = #llvm.linkage<external>, sym_name = "no_cases"}> ({
  ^bb0(%x: i32):
    "llvm.switch"(%x)[^bb1] <{case_operand_segments = array<i32>, operandSegmentSizes = array<i32: 1, 0, 0>}> : (i32) -> ()
  ^bb1:
    "llvm.return"(%x) : (i32) -> ()
  }) : () -> ()
  // Cases with no forwarded operands, and branch weights on the side.
  "llvm.func"() <{function_type = !llvm.func<i32 (i32)>, linkage = #llvm.linkage<external>, sym_name = "weighted"}> ({
  ^bb0(%x: i32):
    "llvm.switch"(%x)[^bb1, ^bb2, ^bb3] <{branch_weights = array<i32: 1, 2, 3>, case_operand_segments = array<i32: 0, 0>, case_values = dense<[13, 35]> : vector<2xi32>, operandSegmentSizes = array<i32: 1, 0, 0>}> : (i32) -> ()
  ^bb1:
    "llvm.return"(%x) : (i32) -> ()
  ^bb2:
    "llvm.return"(%x) : (i32) -> ()
  ^bb3:
    "llvm.return"(%x) : (i32) -> ()
  }) : () -> ()
  // Operands forwarded to the default destination and to each case, two per
  // case, so `case_operand_segments` and the successors' arguments must agree.
  "llvm.func"() <{function_type = !llvm.func<i32 (i32)>, linkage = #llvm.linkage<external>, sym_name = "forwarding"}> ({
  ^bb0(%x: i32):
    %c = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    "llvm.switch"(%x, %c, %x, %c, %c, %x)[^bb1, ^bb2, ^bb2] <{case_operand_segments = array<i32: 2, 2>, case_values = dense<[5, 0]> : vector<2xi32>, operandSegmentSizes = array<i32: 1, 1, 4>}> : (i32, i32, i32, i32, i32, i32) -> ()
  ^bb1(%d: i32):
    "llvm.return"(%d) : (i32) -> ()
  ^bb2(%a: i32, %b: i32):
    "llvm.return"(%a) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "llvm.switch"(%{{[a-z0-9_]+}}) [^{{[0-9]+}}] <{"case_operand_segments" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i32) -> ()
// CHECK: "llvm.switch"(%{{[a-z0-9_]+}}) [^{{[0-9]+}}, ^{{[0-9]+}}, ^{{[0-9]+}}] <{"branch_weights" = array<i32: 1, 2, 3>, "case_operand_segments" = array<i32: 0, 0>, "case_values" = dense<[13, 35]> : vector<2xi32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i32) -> ()
// CHECK: "llvm.switch"({{.*}}) [^{{[0-9]+}}, ^{{[0-9]+}}, ^{{[0-9]+}}] <{"case_operand_segments" = array<i32: 2, 2>, "case_values" = dense<[5, 0]> : vector<2xi32>, "operandSegmentSizes" = array<i32: 1, 1, 4>}> : (i32, i32, i32, i32, i32, i32) -> ()
