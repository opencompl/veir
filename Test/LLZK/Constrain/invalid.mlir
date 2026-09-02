// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: Error verifying input program: constrain.eq: Expected 0 result(s)
"builtin.module"() ({
  "function.def"() <{sym_name = "invalid_constrain", function_type = (!felt.type, !felt.type) -> ()}> ({
^bb0(%a: !felt.type, %b: !felt.type):
  %0 = "constrain.eq"(%a, %b) : (!felt.type, !felt.type) -> i32
  "function.return"() : () -> ()
  }) {function.allow_constraint} : () -> ()
}) : () -> ()
