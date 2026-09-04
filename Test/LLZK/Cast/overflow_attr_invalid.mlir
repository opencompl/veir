// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: #cast<overflow ...> expects one of assert, sat, wrap, trunc
"builtin.module"() ({
^bb0(%value: index):
  %0 = "cast.tofelt"(%value) <{overflow = #cast<overflow saturate>}> : (index) -> !felt.type
}) : () -> ()
