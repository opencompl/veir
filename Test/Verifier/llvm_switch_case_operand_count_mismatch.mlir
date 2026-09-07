// RUN: not veir-opt %s 2>&1 | filecheck %s

// The case forwards one operand, but its destination takes two arguments.
"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<i32 (i32)>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  ^bb0(%x: i32):
    "llvm.switch"(%x, %x)[^bb1, ^bb2] <{case_operand_segments = array<i32: 1>, case_values = dense<[5]> : vector<1xi32>, operandSegmentSizes = array<i32: 1, 0, 1>}> : (i32, i32) -> ()
  ^bb1:
    "llvm.return"(%x) : (i32) -> ()
  ^bb2(%a: i32, %b: i32):
    "llvm.return"(%a) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.switch: case 0 operand segment expected operand count 2, got 1
