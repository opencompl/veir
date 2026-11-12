// RUN: not veir-opt %s 2>&1 | filecheck %s

// The operands of `g_ucmp` are in the same type group.

"builtin.module"() ({
  "func.func"() <{sym_name = "bad", function_type = (i32, i64) -> i8}> ({
  ^bb(%a: i32, %b: i64):
    %r = "gmir.g_ucmp"(%a, %b) : (i32, i64) -> i8
    "func.return"(%r) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: gmir.g_ucmp: type mismatch: expected i32, got i64
