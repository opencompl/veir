// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: cir.add: Expected operands to have the same type
"builtin.module"() ({
  %0 = "cir.const"() <{value = #cir.int<1> : !cir.int<s, 32>}> : () -> !cir.int<s, 32>
  %1 = "cir.const"() <{value = #cir.int<1> : !cir.int<u, 32>}> : () -> !cir.int<u, 32>
  %2 = "cir.add"(%0, %1) <{no_signed_wrap = false, no_unsigned_wrap = false, saturated = false}> : (!cir.int<s, 32>, !cir.int<u, 32>) -> !cir.int<s, 32>
}) : () -> ()
