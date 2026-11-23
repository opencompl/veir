// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// Hex case values hold one byte per i8 element, or a single byte for a splat; three bytes fit
// neither two elements nor one.
"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<i32 (i8)>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  ^bb0(%x: i8):
    %c = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    "llvm.switch"(%x)[^bb1, ^bb1, ^bb1] <{case_operand_segments = array<i32: 0, 0>, case_values = dense<"0x010203"> : vector<2xi8>, operandSegmentSizes = array<i32: 1, 0, 0>}> : (i8) -> ()
  ^bb1:
    "llvm.return"(%c) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.switch: expected case_values to be a tensor or vector of 2 i8 value(s), but got dense<"0x010203"> : vector<2xi8>
