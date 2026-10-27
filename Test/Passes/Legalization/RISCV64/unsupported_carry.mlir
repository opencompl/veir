// RUN: not veir-opt %s -p=legalize-riscv64 2>&1 | filecheck %s

// The carry-in of `g_uadde` is zero-extended to the type of the operands, so it cannot be as wide.
"builtin.module"() ({
  "func.func"() <{function_type = (i64, i64, i64) -> (), sym_name = "main"}> ({
  ^bb0(%a: i64, %b: i64, %c: i64):
    %sum, %carry = "gmir.g_uadde"(%a, %b, %c) : (i64, i64, i64) -> (i64, i64)
    "test.test"(%sum, %carry) : (i64, i64) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: unable to legalize gmir.g_uadde: the lowering is not implemented
