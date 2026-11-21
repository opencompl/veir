// RUN: not veir-opt %s -p=llvm-to-gmir,isel-br-riscv64 2>&1 | filecheck %s
// RUN: not veir-opt %s -p=llvm-to-gmir,isel-br-riscv64{strict=false} 2>&1 | filecheck %s

// The pass does not lower `llvm.unreachable`, in either mode.
// CHECK: isel-br-riscv64: cannot lower llvm.unreachable

"builtin.module"() ({
    "func.func"() <{"function_type" = (i64, i1) -> (i64), "sym_name" = "a"}> ({
    ^bb0(%a: i64, %b: i1):
        "llvm.cond_br"(%b, %a) [^bb1, ^bb2] <{"operandSegmentSizes" = array<i32: 1, 1, 0>}> : (i1, i64) -> ()

    ^bb1(%c: i64):
        "func.return"(%c) : (i64) -> ()

    ^bb2:
        "llvm.unreachable"() : () -> ()
    }) : () -> ()
}) : () -> ()
