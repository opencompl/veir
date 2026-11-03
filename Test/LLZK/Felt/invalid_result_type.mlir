// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: Error verifying input program: felt.neg: Expected result type to match operand type
"builtin.module"() ({
  %a = "felt.const"() <{value = #felt<const 1> : !felt.type}> : () -> !felt.type
  %0 = "felt.neg"(%a) : (!felt.type) -> i32
}) : () -> ()
