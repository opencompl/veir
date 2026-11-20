// RUN: not veir-opt %s -p=legalize-riscv64 2>&1 | filecheck %s

// The `i1` carry-in of `g_uadde` is zero-extended to the type of the operands, so they cannot be `i1`.
"builtin.module"() ({
  "func.func"() <{function_type = (i1, i1, i1) -> (), sym_name = "main"}> ({
  ^bb0(%a: i1, %b: i1, %c: i1):
    %sum, %carry = "gmir.g_uadde"(%a, %b, %c) : (i1, i1, i1) -> (i1, i1)
    "test.test"(%sum, %carry) : (i1, i1) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: unable to legalize gmir.g_uadde: the lowering is not implemented
