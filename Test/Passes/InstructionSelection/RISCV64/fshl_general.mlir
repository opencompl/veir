// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

// A funnel shift with distinct data operands is a true funnel shift, not a
// rotate. Lowering it needs a multi-instruction expansion, which we don't
// implement, so isel must leave the intrinsic untouched (no riscv.rol/ror).

"builtin.module"() ({
    "func.func"()  <{function_type = (i64, i64, i64) -> ()}> ({
    ^bb0(%a: i64, %b: i64, %s: i64):
        %r = "llvm.intr.fshl"(%a, %b, %s) : (i64, i64, i64) -> i64
        // CHECK: %{{.*}} = "llvm.intr.fshl"(%{{.*}}, %{{.*}}, %{{.*}}) : (i64, i64, i64) -> i64
        // CHECK-NOT: riscv.rol
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
