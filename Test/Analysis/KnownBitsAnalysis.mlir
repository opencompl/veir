// RUN: veir-opt %s -p=print-known-bits | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = (i8) -> (), sym_name = "known_bits"}> ({
  ^entry(%x : i8):
    // CHECK:      // dataflow.known_bits block argument 0 = i8(zero=0, one=0)
    %c240 = "arith.constant"() <{value = 240 : i8}> : () -> i8
    // CHECK-NEXT: // dataflow.known_bits arith.constant result 0 = i8(zero=15, one=240)
    %anded = "arith.andi"(%x, %c240) : (i8, i8) -> i8
    // CHECK-NEXT: // dataflow.known_bits arith.andi result 0 = i8(zero=15, one=0)
    %c3 = "arith.constant"() <{value = 3 : i8}> : () -> i8
    // CHECK-NEXT: // dataflow.known_bits arith.constant result 0 = i8(zero=252, one=3)
    %ored = "arith.ori"(%anded, %c3) : (i8, i8) -> i8
    // CHECK-NEXT: // dataflow.known_bits arith.ori result 0 = i8(zero=12, one=3)
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
