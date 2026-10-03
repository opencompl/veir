// REQUIRES: llubi
// RUN: not %llubi-interpret %s 2>&1 | filecheck %s

// A negative test of the translator: an operation it cannot translate, here
// `llvm.switch`, must fail the cross-check loudly instead of passing it
// silently. Which operations those are changes as the translator grows, so
// the check only asks that the error come from it.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %v = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    "llvm.switch"(%v)[^dflt] <{case_values = dense<> : tensor<0xi64>, case_operand_segments = array<i32>, operandSegmentSizes = array<i32: 1, 0, 0>}> : (i64) -> ()
  ^dflt:
    "llvm.return"(%v) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: veir2llvm: error:
