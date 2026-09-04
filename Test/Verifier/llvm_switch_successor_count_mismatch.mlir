// RUN: not veir-opt %s 2>&1 | filecheck %s

// Two case operand segments name two cases, so the op needs three successors:
// the default destination and one per case.
"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<i32 (i32)>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  ^bb0(%x: i32):
    "llvm.switch"(%x)[^bb1, ^bb1] <{case_operand_segments = array<i32: 0, 0>, case_values = dense<[5, 0]> : vector<2xi32>, operandSegmentSizes = array<i32: 1, 0, 0>}> : (i32) -> ()
  ^bb1:
    "llvm.return"(%x) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.switch: Expected 3 successor(s)
