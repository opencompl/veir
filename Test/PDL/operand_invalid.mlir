// RUN: not veir-opt %s 2>&1 | filecheck %s

// A `pdl.operand` produces an `!pdl.value` handle, not an arbitrary type.
"builtin.module"() ({
  %0 = "pdl.operand"() : () -> i32
}) : () -> ()

// CHECK: pdl.operand: Expected the result to be of type '!pdl.value'
