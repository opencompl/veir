// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> ()}> ({
    %x = "arith.constant"() <{value = 3 : i32}> : () -> i32
    "io.send"(%x) : (i32) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: io.send: Expected operand 0 to have i8 array type
