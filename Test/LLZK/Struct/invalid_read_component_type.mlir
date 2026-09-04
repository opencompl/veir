// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
^bb0(%component: !felt.type):
  // CHECK: struct.readm: expected operand 0 to have !struct.type
  %0 = "struct.readm"(%component) <{member_name = @field}> : (!felt.type) -> !felt.type
}) : () -> ()
