// RUN: not veir-opt %s -p=isel-br-riscv64 2>&1 | filecheck %s

// `cf.br` is not supported, even to a block without arguments.
// CHECK: isel-br-riscv64: cannot lower a branch other than llvm.br or llvm.cond_br
"builtin.module"() ({
    "func.func"()  <{"function_type" = (i64) -> (i64), "sym_name" = "a"}> ({
    ^bb0(%a: i64):
        "cf.br"() [^bb1] : () -> ()

    ^bb1:
        "func.return"(%a) : (i64) -> ()
    }) : () -> ()
}) : () -> ()
