// RUN: veir-opt %s -p=isel-br-riscv64{strict=false} --print-op-generic | filecheck %s

// With `strict=false`, a branch whose operand does not fit a register survives
// with its target block, while the other branch is lowered.

// CHECK:      "llvm.br"(%{{.*}}) [^{{.*}}] : (i128) -> ()
// CHECK-NEXT: ^{{.*}}(%{{.*}} : i128):
// CHECK-NEXT:   "func.return"
// CHECK:      "riscv_cf.branch"(%{{.*}}) [^{{.*}}] : (!riscv.reg) -> ()
// CHECK-NEXT: ^{{.*}}(%{{.*}} : !riscv.reg):
"builtin.module"() ({
    "func.func"()  <{"function_type" = (i128) -> (i128), "sym_name" = "a"}> ({
    ^bb0(%a: i128):
        "llvm.br"(%a) [^bb1] : (i128) -> ()

    ^bb1(%b: i128):
        "func.return"(%b) : (i128) -> ()
    }) : () -> ()
    "func.func"()  <{"function_type" = (i64) -> (i64), "sym_name" = "b"}> ({
    ^bb0(%a: i64):
        "llvm.br"(%a) [^bb1] : (i64) -> ()

    ^bb1(%b: i64):
        "func.return"(%b) : (i64) -> ()
    }) : () -> ()
}) : () -> ()
