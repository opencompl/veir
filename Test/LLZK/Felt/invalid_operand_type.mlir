// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: Error verifying input program: felt.add: Expected operands to have FeltType
"builtin.module"() ({
  %a = "arith.constant"() <{value = 1 : i32}> : () -> i32
  %0 = "felt.add"(%a, %a) : (i32, i32) -> i32
}) : () -> ()
