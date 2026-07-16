// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// Sign extension is idempotent: `riscv.sextw (riscv.sextw x) -> riscv.sextw x`.

"builtin.module"() ({
  "func.func"() <{function_type = (!riscv.reg) -> !riscv.reg, sym_name = "foo"}> ({
  ^bb0(%x: !riscv.reg):
    %inner = "riscv.sextw"(%x) : (!riscv.reg) -> !riscv.reg
    %outer = "riscv.sextw"(%inner) : (!riscv.reg) -> !riscv.reg
    "func.return"(%outer) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      ^{{.*}}(%[[X:.*]] : !riscv.reg):
// CHECK-NEXT: %[[INNER:.*]] = "riscv.sextw"(%[[X]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: "func.return"(%[[INNER]]) : (!riscv.reg) -> ()
