// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "func.func"() <{sym_name = "f", function_type = (i32, i16) -> ()}> ({
  ^bb0(%a: i32, %b: i64):
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: func.func: type of entry block argument #1(i64) must match the type of the corresponding argument in function signature(i16)
