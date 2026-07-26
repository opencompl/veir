// RUN: not veir-opt %s 2>&1 | filecheck %s

// An `arith` operation may not produce an `i0` value.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = (i8) -> ()}> ({
  ^bb0(%arg0: i8):
    %x = "arith.trunci"(%arg0) : (i8) -> i0
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: arith.trunci: result 0 has forbidden i0 type
