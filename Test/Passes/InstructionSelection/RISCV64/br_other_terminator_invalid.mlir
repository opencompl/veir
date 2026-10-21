// RUN: not veir-opt %s -p=isel-br-riscv64 2>&1 | filecheck %s

// `cf.br` is not supported.
// CHECK: isel-br-riscv64: cannot lower a branch other than llvm.br or llvm.cond_br
"builtin.module"() ({
    "func.func"()  <{"function_type" = (i64) -> (i64), "sym_name" = "a"}> ({
    ^bb0(%a: i64):
        "cf.br"(%a) [^bb1] : (i64) -> ()

    ^bb1(%b: i64):
        "func.return"(%b) : (i64) -> ()
    }) : () -> ()
}) : () -> ()
