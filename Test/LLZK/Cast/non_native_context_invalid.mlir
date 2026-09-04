// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: Error verifying input program: cast.toindex: cannot be used within a 'function.def' without the 'function.allow_non_native_field_ops' attribute
"builtin.module"() ({
  "function.def"() <{sym_name = "missing_permission", function_type = (!felt.type) -> ()}> ({
  ^bb0(%value: !felt.type):
    %0 = "cast.toindex"(%value) : (!felt.type) -> index
    "function.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
