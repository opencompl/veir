// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: Error verifying input program: felt.add: Expected operands to have the same type
"builtin.module"() ({
  %a = "felt.const"() <{value = #felt<const 1 : !felt.type<"babybear">>}> : () -> !felt.type<"babybear">
  %b = "felt.const"() <{value = #felt<const 2 : !felt.type<"bn254">>}> : () -> !felt.type<"bn254">
  %0 = "felt.add"(%a, %b) : (!felt.type<"babybear">, !felt.type<"bn254">) -> !felt.type<"babybear">
}) : () -> ()
