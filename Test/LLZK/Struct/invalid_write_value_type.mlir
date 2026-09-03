// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
^bb0(%component: !struct.type<@Example>, %value: f32):
  // CHECK: struct.writem: expected operand 1 to have a supported LLZK type
  "struct.writem"(%component, %value) <{member_name = @field}> : (!struct.type<@Example>, f32) -> ()
}) : () -> ()
