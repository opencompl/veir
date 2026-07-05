// RUN: veir-opt %s -p=riscv-combine | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = (!riscv.reg) -> !riscv.reg}> ({
  ^bb0(%x: !riscv.reg):
    %inner = "riscv.zextw"(%x) : (!riscv.reg) -> !riscv.reg
    %outer = "riscv.zextw"(%inner) : (!riscv.reg) -> !riscv.reg
    "func.return"(%outer) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      ^{{.*}}(%[[X:.*]] : !riscv.reg):
// CHECK-NEXT: %[[INNER:.*]] = "riscv.zextw"(%[[X]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: "func.return"(%[[INNER]]) : (!riscv.reg) -> ()
