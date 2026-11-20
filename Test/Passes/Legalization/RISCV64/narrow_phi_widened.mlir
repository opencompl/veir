// RUN: veir-opt %s -p=llvm-to-gmir,legalize-riscv64 | filecheck %s

// The legalizer widens a narrow phi to the legal width.

// CHECK: ^{{.*}}(%{{.*}} : i64):

"builtin.module"() ({
  "func.func"() <{sym_name = "f", function_type = (i32) -> i32}> ({
  ^bb0(%a : i32):
    "llvm.br"(%a) [^next] : (i32) -> ()
  ^next(%b : i32):
    "func.return"(%b) : (i32) -> ()
  }) : () -> ()
}) : () -> ()
