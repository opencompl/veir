// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: function.return operand 0 type does not match the function's declared result type
"builtin.module"() ({
  "function.def"() <{sym_name = "type_mismatch", function_type = (i1) -> !felt.type}> ({
  ^entry(%arg: i1):
    "function.return"(%arg) : (i1) -> ()
  }) : () -> ()
}) : () -> ()
