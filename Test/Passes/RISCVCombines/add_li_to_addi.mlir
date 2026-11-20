// RUN: veir-opt %s -p=riscv-combine,dce | filecheck %s

// `add x, (li c)` and `add (li c), x` become `addi x, c` when `c` fits a
// signed 12-bit immediate. Constants just outside that range are kept in a
// register.

"builtin.module"() ({
  "func.func"() <{function_type = (!riscv.reg) -> (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg), sym_name = "add_li"}> ({
  ^bb0(%x: !riscv.reg):
    %max = "riscv.li"() <{"value" = 2047 : i64}> : () -> !riscv.reg
    %a = "riscv.add"(%x, %max) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %min = "riscv.li"() <{"value" = -2048 : i64}> : () -> !riscv.reg
    %b = "riscv.add"(%min, %x) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %big = "riscv.li"() <{"value" = 2048 : i64}> : () -> !riscv.reg
    %c = "riscv.add"(%x, %big) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %small = "riscv.li"() <{"value" = -2049 : i64}> : () -> !riscv.reg
    %d = "riscv.add"(%small, %x) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %one = "riscv.li"() <{"value" = 1 : i64}> : () -> !riscv.reg
    %e = "riscv.add"(%x, %one) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "func.return"(%a, %b, %c, %d, %e) : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: func.func @add_li(
// CHECK-DAG: %[[A:[^ ]*]] = "riscv.addi"(%[[X:[^)]*]]) <{"value" = 2047 : i64}>
// CHECK-DAG: %[[B:[^ ]*]] = "riscv.addi"(%[[X]]) <{"value" = -2048 : i64}>
// CHECK-DAG: %[[BIG:[^ ]*]] = "riscv.li"() <{"value" = 2048 : i64}>
// CHECK-DAG: %[[C:[^ ]*]] = "riscv.add"(%[[X]], %[[BIG]])
// CHECK-DAG: %[[SMALL:[^ ]*]] = "riscv.li"() <{"value" = -2049 : i64}>
// CHECK-DAG: %[[D:[^ ]*]] = "riscv.add"(%[[SMALL]], %[[X]])
// CHECK-DAG: %[[E:[^ ]*]] = "riscv.addi"(%[[X]]) <{"value" = 1 : i64}>
// CHECK: "func.return"(%[[A]], %[[B]], %[[C]], %[[D]], %[[E]])
