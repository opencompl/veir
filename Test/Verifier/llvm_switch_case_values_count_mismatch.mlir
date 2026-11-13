// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// Three case values, but two cases.
"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<i32 (i32)>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  ^bb0(%x: i32):
    %c = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    "llvm.switch"(%x)[^bb1, ^bb1, ^bb1] <{case_operand_segments = array<i32: 0, 0>, case_values = dense<[5, 6, 7]> : vector<3xi32>, operandSegmentSizes = array<i32: 1, 0, 0>}> : (i32) -> ()
  ^bb1:
    "llvm.return"(%c) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.switch: expected case_values to be a tensor or vector of 2 i32 value(s), but got dense<[5, 6, 7]> : vector<3xi32>
