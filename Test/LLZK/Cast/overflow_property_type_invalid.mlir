// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: error: cast.tofelt: expected 'overflow' to be a #cast<overflow ...> attribute
"builtin.module"() ({
^bb0(%value: index):
  %0 = "cast.tofelt"(%value) <{overflow = 1 : i32}> : (index) -> !felt.type
}) : () -> ()
