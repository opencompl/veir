// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: Error verifying input program: bool.assert: Expected 0 result(s)
"builtin.module"() ({
  "function.def"() <{sym_name = "invalid_bool", function_type = (i1) -> ()}> ({
^bb0(%a: i1):
  %0 = "bool.assert"(%a) : (i1) -> i1
  "function.return"() : () -> ()
  }) {function.allow_non_native_field_ops} : () -> ()
}) : () -> ()
