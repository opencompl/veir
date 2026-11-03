// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: Error verifying input program: felt.add: Expected 2 operand(s)
"builtin.module"() ({
  %a = "felt.const"() <{value = #felt<const 1> : !felt.type}> : () -> !felt.type
  %0 = "felt.add"(%a) : (!felt.type) -> !felt.type
}) : () -> ()
