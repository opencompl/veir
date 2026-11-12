// RUN: not veir-opt %s -p=llvm-to-gmir,legalize-riscv64 2>&1 | filecheck %s

// The legalizer only runs the rules proved to refine the module. Widening a block argument is not
// one of them, so a narrow phi is rejected.

// CHECK: unable to legalize a block argument of type i32

"builtin.module"() ({
  "func.func"() <{sym_name = "f", function_type = (i32) -> i32}> ({
  ^bb0(%a : i32):
    "llvm.br"(%a) [^next] : (i32) -> ()
  ^next(%b : i32):
    "func.return"(%b) : (i32) -> ()
  }) : () -> ()
}) : () -> ()
