// RUN: not veir-opt %s -p=llvm-to-gmir,legalize-riscv64{strict} 2>&1 | filecheck %s
// RUN: veir-opt %s -p=llvm-to-gmir,legalize-riscv64 | filecheck %s --check-prefix=LAX

// The strict legalizer only runs the rules proved to refine the module. Widening a block
// argument is not one of them, so a narrow phi is rejected, while the default pass widens it.

// CHECK: unable to legalize a block argument of type i32

// LAX: ^{{.*}}(%{{.*}}: i64):

"builtin.module"() ({
  "func.func"() <{sym_name = "f", function_type = (i32) -> i32}> ({
  ^bb0(%a : i32):
    "llvm.br"(%a) [^next] : (i32) -> ()
  ^next(%b : i32):
    "func.return"(%b) : (i32) -> ()
  }) : () -> ()
}) : () -> ()
