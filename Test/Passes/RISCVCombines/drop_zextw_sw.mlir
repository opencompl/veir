// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `riscv.sw` only writes bits 31:0 of its value operand, so a `riscv.zextw`
// feeding that operand is redundant and gets dropped. The address operand is a
// full 64-bit pointer and must be left untouched, even if it too happens to be
// fed by a `riscv.zextw`.

"builtin.module"() ({
  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> (), sym_name = "foo"}> ({
  ^bb0(%addr: !riscv.reg, %val: !riscv.reg):
    %zval = "riscv.zextw"(%val) : (!riscv.reg) -> !riscv.reg
    "riscv.sw"(%addr, %zval) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
    "func.return"() : () -> ()
  }) : () -> ()

  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> (), sym_name = "bar"}> ({
  ^bb0(%addr: !riscv.reg, %val: !riscv.reg):
    %zaddr = "riscv.zextw"(%addr) : (!riscv.reg) -> !riscv.reg
    %zval = "riscv.zextw"(%val) : (!riscv.reg) -> !riscv.reg
    "riscv.sw"(%zaddr, %zval) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// riscv-combine alone (no dce) leaves the now-dead `zextw` in place; what matters
// is that `riscv.sw` itself no longer reads through it.
// CHECK:      ^{{.*}}(%[[ADDR:.*]] : !riscv.reg, %[[VAL:.*]] : !riscv.reg):
// CHECK:      "riscv.sw"(%[[ADDR]], %[[VAL]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT: "func.return"() : () -> ()

// The address operand's `zextw` must survive unchanged (only the value operand
// is stripped).
// CHECK:      ^{{.*}}(%[[ADDR2:.*]] : !riscv.reg, %[[VAL2:.*]] : !riscv.reg):
// CHECK:      %[[ZADDR2:.*]] = "riscv.zextw"(%[[ADDR2]])
// CHECK:      "riscv.sw"(%[[ZADDR2]], %[[VAL2]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT: "func.return"() : () -> ()
