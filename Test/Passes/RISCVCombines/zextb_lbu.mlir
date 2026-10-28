// RUN: veir-opt %s -p=riscv-combine,dce | filecheck %s

// `lbu` already produces a zero-extended byte; only that load-fed extension
// is removed.

"builtin.module"() ({
  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> (!riscv.reg, !riscv.reg), sym_name = "zextb_lbu"}> ({
  ^bb0(%addr: !riscv.reg, %other: !riscv.reg):
    %unsigned = "riscv.lbu"(%addr) <{"value" = 11 : i64}> : (!riscv.reg) -> !riscv.reg
    %already_unsigned = "riscv.zextb"(%unsigned) : (!riscv.reg) -> !riscv.reg
    %unchanged = "riscv.zextb"(%other) : (!riscv.reg) -> !riscv.reg
    "func.return"(%already_unsigned, %unchanged) : (!riscv.reg, !riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: func.func @zextb_lbu(%{{[^:]*}}: !riscv.reg, %[[OTHER:[^:]*]]: !riscv.reg)
// CHECK: %[[UNSIGNED:[^ ]*]] = "riscv.lbu"(%[[ADDR:[^)]*]]) <{"value" = 11 : i64}>
// CHECK: %[[UNCHANGED:[^ ]*]] = "riscv.zextb"(%[[OTHER]])
// CHECK: "func.return"(%[[UNSIGNED]], %[[UNCHANGED]])
