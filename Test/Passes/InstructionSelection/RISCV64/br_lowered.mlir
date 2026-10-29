// RUN: veir-opt %s -p=llvm-to-gmir,isel-br-riscv64 --print-op-generic | filecheck %s

// A RISC-V branch and a register block argument are already lowered, and the
// pass leaves them alone.

// CHECK:      "riscv_cf.branch"(%{{.*}}) [^{{.*}}] : (!riscv.reg) -> ()
// CHECK-NEXT: ^{{.*}}(%{{.*}} : !riscv.reg):
// CHECK-NEXT:   "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> i64
// CHECK-NEXT:   "func.return"
"builtin.module"() ({
    "func.func"()  <{"function_type" = (i64) -> (i64), "sym_name" = "a"}> ({
    ^bb0(%a: i64):
        %r = "builtin.unrealized_conversion_cast"(%a) : (i64) -> !riscv.reg
        "riscv_cf.branch"(%r) [^bb1] : (!riscv.reg) -> ()

    ^bb1(%b: !riscv.reg):
        %v = "builtin.unrealized_conversion_cast"(%b) : (!riscv.reg) -> i64
        "func.return"(%v) : (i64) -> ()
    }) : () -> ()
}) : () -> ()
