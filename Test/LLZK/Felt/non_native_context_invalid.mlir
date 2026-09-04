// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: Error verifying input program: felt.pow: cannot be used within a 'function.def' without the 'function.allow_non_native_field_ops' attribute
"builtin.module"() ({
  "function.def"() <{sym_name = "missing_permission", function_type = (!felt.type, !felt.type) -> (!felt.type)}> ({
  ^bb0(%base: !felt.type, %exponent: !felt.type):
    %0 = "felt.pow"(%base, %exponent) : (!felt.type, !felt.type) -> !felt.type
    "function.return"(%0) : (!felt.type) -> ()
  }) : () -> ()
}) : () -> ()
