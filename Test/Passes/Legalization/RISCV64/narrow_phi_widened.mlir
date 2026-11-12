// RUN: veir-opt %s -p=llvm-to-gmir,legalize-riscv64 | filecheck %s

// A narrow phi is widened to the legal width by `legalizeBlockArguments`, which the soundness of
// the pass assumes (`legalizeBlockArguments_sound`).

// CHECK: ^{{.*}}(%{{.*}} : i64):

"builtin.module"() ({
  "func.func"() <{sym_name = "f", function_type = (i32) -> i32}> ({
  ^bb0(%a : i32):
    "llvm.br"(%a) [^next] : (i32) -> ()
  ^next(%b : i32):
    "func.return"(%b) : (i32) -> ()
  }) : () -> ()
}) : () -> ()
