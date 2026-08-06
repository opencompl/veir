// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `riscv.sw` only writes bits 31:0 of its value operand, so a `riscv.zextw`
// feeding that operand is redundant and gets dropped. The address operand is a
// full 64-bit pointer and must be left untouched, even if it too happens to be
// fed by a `riscv.zextw`.
//
// RISC-V stores take the stored value as operand 0 and the base address as
// operand 1; see `Test/Interpreter/RISCV/sw.mlir`.

"builtin.module"() ({
  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> (), sym_name = "foo"}> ({
  ^bb0(%addr: !riscv.reg, %val: !riscv.reg):
    %zval = "riscv.zextw"(%val) : (!riscv.reg) -> !riscv.reg
    "riscv.sw"(%zval, %addr) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
    "func.return"() : () -> ()
  }) : () -> ()

  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> (), sym_name = "bar"}> ({
  ^bb0(%addr: !riscv.reg, %val: !riscv.reg):
    %zaddr = "riscv.zextw"(%addr) : (!riscv.reg) -> !riscv.reg
    %zval = "riscv.zextw"(%val) : (!riscv.reg) -> !riscv.reg
    "riscv.sw"(%zval, %zaddr) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// What matters is that `riscv.sw` no longer reads through the `zextw`; the
// greedy driver then erases it as trivially dead.
// CHECK:      ^{{.*}}(%[[ADDR:.*]] : !riscv.reg, %[[VAL:.*]] : !riscv.reg):
// CHECK:      "riscv.sw"(%[[VAL]], %[[ADDR]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT: "func.return"() : () -> ()

// The address operand's `zextw` must survive unchanged (only the value operand
// is stripped).
// CHECK:      ^{{.*}}(%[[ADDR2:.*]] : !riscv.reg, %[[VAL2:.*]] : !riscv.reg):
// CHECK:      %[[ZADDR2:.*]] = "riscv.zextw"(%[[ADDR2]])
// CHECK:      "riscv.sw"(%[[VAL2]], %[[ZADDR2]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT: "func.return"() : () -> ()
