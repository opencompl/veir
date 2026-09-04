// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: Error verifying input program: bool.and: cannot be used within a 'function.def' without the 'function.allow_non_native_field_ops' attribute
"builtin.module"() ({
  "function.def"() <{sym_name = "missing_permission", function_type = (i1, i1) -> ()}> ({
  ^bb0(%a: i1, %b: i1):
    %0 = "bool.and"(%a, %b) : (i1, i1) -> i1
    "function.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
