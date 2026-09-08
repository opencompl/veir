// RUN: veir-opt %s -p=riscv-combine,dce | filecheck %s

// `sb` consumes only the low byte of its value operand. A `sextw` there is
// redundant, while an extension feeding the address must remain.

"builtin.module"() ({
  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> (), sym_name = "drop_sextw_sb"}> ({
  ^bb0(%addr: !riscv.reg, %value: !riscv.reg):
    %extended_value = "riscv.sextw"(%value) : (!riscv.reg) -> !riscv.reg
    "riscv.sb"(%extended_value, %addr) <{"value" = 3 : i64}> : (!riscv.reg, !riscv.reg) -> ()
    %extended_addr = "riscv.sextw"(%addr) : (!riscv.reg) -> !riscv.reg
    "riscv.sb"(%value, %extended_addr) <{"value" = 4 : i64, volatile_}> : (!riscv.reg, !riscv.reg) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: "sym_name" = "drop_sextw_sb"
// CHECK: "riscv.sb"(%[[VALUE:.*]], %[[ADDR:.*]]) <{"value" = 3 : i64}>
// CHECK: %[[SADDR:.*]] = "riscv.sextw"(%[[ADDR]])
// CHECK-NEXT: "riscv.sb"(%[[VALUE]], %[[SADDR]]) <{"value" = 4 : i64, volatile_}>
