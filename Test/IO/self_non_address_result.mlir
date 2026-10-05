// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> ()}> ({
    %a = "io.self"() : () -> i32
    // CHECK: io.self: Expected result 0 to have !io.address type
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
