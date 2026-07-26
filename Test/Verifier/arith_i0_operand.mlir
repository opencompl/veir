// RUN: not veir-opt %s 2>&1 | filecheck %s

// An `arith` operation may not accept an `i0` value.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = (i0) -> ()}> ({
  ^bb0(%arg0: i0):
    %x = "arith.addi"(%arg0, %arg0) : (i0, i0) -> i0
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: arith.addi: operand 0 has forbidden i0 type
