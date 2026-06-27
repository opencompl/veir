// RUN: not veir-opt %s 2>&1 | filecheck %s

// SSA requires that each name is assigned exactly once. Defining %a twice is
// rejected by the parser, before verification runs.

"builtin.module"() ({
  "func.func"() <{function_type = () -> i32, sym_name = "main"}> ({
  ^bb0():
    %a = "arith.constant"() <{"value" = 0 : i32}> : () -> i32
    %a = "arith.constant"() <{"value" = 1 : i32}> : () -> i32
    "func.return"(%a) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: value %a has already been defined
