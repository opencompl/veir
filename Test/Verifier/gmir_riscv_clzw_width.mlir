// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "bad", function_type = (i32) -> i32}> ({
  ^bb(%a: i32):
    %r = "gmir_riscv.g_clzw"(%a) : (i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: gmir_riscv.g_clzw: Expected i64 operands and result
