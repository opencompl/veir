// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// 256 does not fit in i8, whether read as signed or unsigned.
"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<i32 (i8)>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  ^bb0(%x: i8):
    %c = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    "llvm.switch"(%x)[^bb1, ^bb1, ^bb1] <{case_operand_segments = array<i32: 0, 0>, case_values = dense<[5, 256]> : vector<2xi8>, operandSegmentSizes = array<i32: 1, 0, 0>}> : (i8) -> ()
  ^bb1:
    "llvm.return"(%c) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.switch: expected case_values to be a tensor or vector of 2 i8 value(s), but got dense<[5, 256]> : vector<2xi8>
