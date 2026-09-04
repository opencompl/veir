// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: cir: expected no properties, but got 1 property
"builtin.module"() ({
  %0 = "cir.const"() <{value = #cir.int<1> : !cir.int<s, 32>}> : () -> !cir.int<s, 32>
  %1 = "cir.mul"(%0, %0) <{unexpected}> : (!cir.int<s, 32>, !cir.int<s, 32>) -> !cir.int<s, 32>
}) : () -> ()
