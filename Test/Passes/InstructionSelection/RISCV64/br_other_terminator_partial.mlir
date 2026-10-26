// RUN: veir-opt %s -p=isel-br-riscv64{strict=false} --print-op-generic | filecheck %s

// With `strict=false`, a block that a `cf.br` branches to keeps its argument,
// so the `llvm.br` to it survives as well, while the other branch is lowered.

// CHECK:      "llvm.br"(%{{.*}}) [^{{.*}}] : (i64) -> ()
// CHECK:      "cf.br"(%{{.*}}) [^{{.*}}] : (i64) -> ()
// CHECK-NEXT: ^{{.*}}(%{{.*}} : i64):
// CHECK-NEXT:   "func.return"
// CHECK:      "riscv_cf.branch"(%{{.*}}) [^{{.*}}] : (!riscv.reg) -> ()
// CHECK-NEXT: ^{{.*}}(%{{.*}} : !riscv.reg):
"builtin.module"() ({
    "func.func"()  <{"function_type" = (i1, i64) -> (i64), "sym_name" = "a"}> ({
    ^bb0(%c: i1, %a: i64):
        "llvm.cond_br"(%c) [^bb1, ^bb2] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()

    ^bb1:
        "llvm.br"(%a) [^bb3] : (i64) -> ()

    ^bb2:
        "cf.br"(%a) [^bb3] : (i64) -> ()

    ^bb3(%b: i64):
        "func.return"(%b) : (i64) -> ()
    }) : () -> ()
    "func.func"()  <{"function_type" = (i64) -> (i64), "sym_name" = "b"}> ({
    ^bb0(%a: i64):
        "llvm.br"(%a) [^bb1] : (i64) -> ()

    ^bb1(%b: i64):
        "func.return"(%b) : (i64) -> ()
    }) : () -> ()
}) : () -> ()
