// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  // CHECK: Error verifying input program: function.def: entry block argument 0 type does not match the function's declared input type
  "function.def"() <{sym_name = "bad", function_type = (!felt.type) -> ()}> ({
  ^entry(%arg0: i32):
    "function.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
