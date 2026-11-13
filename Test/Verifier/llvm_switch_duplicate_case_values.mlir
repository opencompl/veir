// RUN: not veir-opt %s 2>&1 | filecheck %s

// 255 and -1 are the same i8 value. Upstream MLIR accepts duplicate case values, but LLVM IR
// rejects them, so VeIR does too: the switch could not be translated to LLVM IR.
"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<i32 (i8)>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  ^bb0(%x: i8):
    %c = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    "llvm.switch"(%x)[^bb1, ^bb1, ^bb1] <{case_operand_segments = array<i32: 0, 0>, case_values = dense<[255, -1]> : vector<2xi8>, operandSegmentSizes = array<i32: 1, 0, 0>}> : (i8) -> ()
  ^bb1:
    "llvm.return"(%c) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.switch: duplicate case value -1
