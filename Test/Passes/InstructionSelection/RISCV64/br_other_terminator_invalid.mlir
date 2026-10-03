// RUN: not veir-opt %s -p=isel-br-riscv64 2>&1 | filecheck %s

// The arguments of `^bb1` would become registers, but `cf.br` still passes an integer.
// CHECK: isel-br-riscv64: only llvm.br and llvm.cond_br may have successors
"builtin.module"() ({
    "func.func"()  <{"function_type" = (i64) -> (i64), "sym_name" = "a"}> ({
    ^bb0(%a: i64):
        "cf.br"(%a) [^bb1] : (i64) -> ()

    ^bb1(%b: i64):
        "func.return"(%b) : (i64) -> ()
    }) : () -> ()
}) : () -> ()
