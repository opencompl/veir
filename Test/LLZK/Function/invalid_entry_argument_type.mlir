// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  // CHECK: Error verifying input program: function.def: type of entry block argument #0(i32) must match the type of the corresponding argument in function signature(!felt.type)
  "function.def"() <{sym_name = "bad", function_type = (!felt.type) -> ()}> ({
  ^entry(%arg0: i32):
    "function.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
