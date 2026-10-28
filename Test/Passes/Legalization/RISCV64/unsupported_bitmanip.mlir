// RUN: not veir-opt %s -p=legalize-riscv64 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = (i128) -> (), sym_name = "main"}> ({
  ^bb0(%x: i128):
    %ctpop = "gmir.g_ctpop"(%x) : (i128) -> i128
    "test.test"(%ctpop) : (i128) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// TODO: Implement narrowing for legalization.
// CHECK: unable to legalize gmir.g_ctpop: no legalization rule matches
