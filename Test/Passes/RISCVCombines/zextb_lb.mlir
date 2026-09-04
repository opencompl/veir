// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `zextb(lb)` becomes `lbu` only for non-volatile loads. The replacement
// preserves the load's memory properties, including its offset. The combine's
// greedy driver removes the now-dead original non-volatile load itself.

"builtin.module"() ({
  "func.func"() <{function_type = (!riscv.reg) -> (!riscv.reg, !riscv.reg), sym_name = "zextb_lb"}> ({
  ^bb0(%addr: !riscv.reg):
    %plain_lb = "riscv.lb"(%addr) <{"value" = 7 : i64}> : (!riscv.reg) -> !riscv.reg
    %plain = "riscv.zextb"(%plain_lb) : (!riscv.reg) -> !riscv.reg
    %volatile_lb = "riscv.lb"(%addr) <{"value" = 9 : i64, volatile_}> : (!riscv.reg) -> !riscv.reg
    %volatile = "riscv.zextb"(%volatile_lb) : (!riscv.reg) -> !riscv.reg
    "func.return"(%plain, %volatile) : (!riscv.reg, !riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: "sym_name" = "zextb_lb"
// CHECK: %[[PLAIN:[^ ]*]] = "riscv.lbu"(%[[ADDR:[^)]*]]) <{"value" = 7 : i64}>
// CHECK: %[[VOLATILE_LB:[^ ]*]] = "riscv.lb"(%[[ADDR]]) <{"value" = 9 : i64, volatile_}>
// CHECK-NEXT: %[[VOLATILE:[^ ]*]] = "riscv.zextb"(%[[VOLATILE_LB]])
// CHECK: "func.return"(%[[PLAIN]], %[[VOLATILE]])
