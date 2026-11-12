// RUN: not veir-opt %s 2>&1 | filecheck %s

// As for `llvm.intr.scmp`, the result must be at least `i2`, to hold -1, 0, and 1.

"builtin.module"() ({
  "func.func"() <{sym_name = "bad", function_type = (i32, i32) -> i1}> ({
  ^bb(%a: i32, %b: i32):
    %r = "gmir.g_scmp"(%a, %b) : (i32, i32) -> i1
    "func.return"(%r) : (i1) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: gmir.g_scmp: Expected result type to be at least i2
