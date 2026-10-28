// RUN: not veir-opt %s -p=llvm-to-gmir,isel-br-riscv64 2>&1 | filecheck %s

// `cf.cond_br` is not supported.
// CHECK: isel-br-riscv64: cannot lower a branch other than g_br or g_brcond
"builtin.module"() ({
    "func.func"()  <{"function_type" = (i1, i64) -> (i64), "sym_name" = "a"}> ({
    ^bb0(%c: i1, %a: i64):
        "cf.cond_br"(%c, %a, %a) [^bb1, ^bb2] <{"operandSegmentSizes" = array<i32: 1, 1, 1>}> : (i1, i64, i64) -> ()

    ^bb1(%b: i64):
        "func.return"(%b) : (i64) -> ()

    ^bb2(%d: i64):
        "func.return"(%d) : (i64) -> ()
    }) : () -> ()
}) : () -> ()
