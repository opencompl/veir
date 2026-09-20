// RUN: not veir-opt %s -p=isel-br-riscv64 --disable-verifiers 2>&1 | filecheck %s

// The arguments of the entry block are those of the function, and stay as they are.
// The verifier rejects this module first, so the test runs without it.
// CHECK: isel-br-riscv64: the entry block of a region is branched to
"builtin.module"() ({
    "func.func"()  <{"function_type" = (i64) -> (i64), "sym_name" = "a"}> ({
    ^bb0(%a: i64):
        "llvm.br"(%a) [^bb0] : (i64) -> ()
    }) : () -> ()
}) : () -> ()
