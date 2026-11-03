// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: Error verifying input program: smt.bv.neg: Expected operand 0 to have a bit-vector sort
"builtin.module"() ({
  "func.func"() <{sym_name = "f", function_type = (i8) -> i8}> ({
  ^bb0(%arg0: i8):
    %0 = "smt.bv.neg"(%arg0) : (i8) -> i8
    "func.return"(%0) : (i8) -> ()
  }) : () -> ()
}) : () -> ()
