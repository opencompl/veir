// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: Error verifying input program: bool.assert: Expected operand 0 to have i1 type
"builtin.module"() ({
^bb0(%condition: !felt.type):
  "bool.assert"(%condition) : (!felt.type) -> ()
}) : () -> ()
