// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: cir.const: Expected result type to match the constant's type
"builtin.module"() ({
  %0 = "cir.const"() <{value = #cir.int<1> : !cir.int<s, 32>}> : () -> !cir.int<u, 32>
}) : () -> ()
