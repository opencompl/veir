// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: Error verifying input program: felt.const: Expected result type to match the constant's type
"builtin.module"() ({
  %0 = "felt.const"() <{value = #felt<const 1 : !felt.type<"babybear">>}> : () -> !felt.type<"bn254">
}) : () -> ()
