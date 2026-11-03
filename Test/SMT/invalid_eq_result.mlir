// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: Error verifying input program: smt.eq: Expected result 0 to have type !smt.bool
"builtin.module"() ({
  "func.func"() <{sym_name = "f", function_type = (!smt.bv<8>) -> !smt.bv<8>}> ({
  ^bb0(%arg0: !smt.bv<8>):
    %0 = "smt.eq"(%arg0, %arg0) : (!smt.bv<8>, !smt.bv<8>) -> !smt.bv<8>
    "func.return"(%0) : (!smt.bv<8>) -> ()
  }) : () -> ()
}) : () -> ()
