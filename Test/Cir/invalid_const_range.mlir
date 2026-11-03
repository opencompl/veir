// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: cir.const: constant value 128 does not fit in !cir.int<s, 8>
"builtin.module"() ({
  %0 = "cir.const"() <{value = #cir.int<128> : !cir.int<s, 8>}> : () -> !cir.int<s, 8>
}) : () -> ()
