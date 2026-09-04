// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: cir.cmp: invalid kind 7
"builtin.module"() ({
  %0 = "cir.const"() <{value = #cir.int<1> : !cir.int<s, 32>}> : () -> !cir.int<s, 32>
  %1 = "cir.cmp"(%0, %0) <{kind = 7 : i32}> : (!cir.int<s, 32>, !cir.int<s, 32>) -> !cir.bool
}) : () -> ()
