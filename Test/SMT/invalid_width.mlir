// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: Error verifying input program: smt.bv.add: Expected operands to have the same bit-vector width
"builtin.module"() ({
  "func.func"() <{sym_name = "f", function_type = (!smt.bv<8>, !smt.bv<16>) -> !smt.bv<8>}> ({
  ^bb0(%arg0: !smt.bv<8>, %arg1: !smt.bv<16>):
    %0 = "smt.bv.add"(%arg0, %arg1) : (!smt.bv<8>, !smt.bv<16>) -> !smt.bv<8>
    "func.return"(%0) : (!smt.bv<8>) -> ()
  }) : () -> ()
}) : () -> ()
