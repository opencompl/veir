// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `riscv.sw` only writes bits 31:0 of its value operand, so a `riscv.zextw`
// feeding that operand is redundant and gets dropped. The address operand is a
// full 64-bit pointer and must be left untouched, even if it too happens to be
// fed by a `riscv.zextw`.
//
// The store's operand order is *value first, address second* (the isel and
// interpreter convention): `"riscv.sw"(%value, %address)`.

"builtin.module"() ({
  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> ()}> ({
  ^bb0(%val: !riscv.reg, %addr: !riscv.reg):
    %zval = "riscv.zextw"(%val) : (!riscv.reg) -> !riscv.reg
    "riscv.sw"(%zval, %addr) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
    "func.return"() : () -> ()
  }) : () -> ()

  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> ()}> ({
  ^bb0(%val: !riscv.reg, %addr: !riscv.reg):
    %zval = "riscv.zextw"(%val) : (!riscv.reg) -> !riscv.reg
    %zaddr = "riscv.zextw"(%addr) : (!riscv.reg) -> !riscv.reg
    "riscv.sw"(%zval, %zaddr) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// riscv-combine alone (no dce) leaves the now-dead `zextw` in place; what matters
// is that `riscv.sw` itself no longer reads through it on its value operand.
// CHECK:      ^{{.*}}(%[[VAL:.*]] : !riscv.reg, %[[ADDR:.*]] : !riscv.reg):
// CHECK:      "riscv.sw"(%[[VAL]], %[[ADDR]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT: "func.return"() : () -> ()

// The address operand's `zextw` must survive unchanged (only the value operand
// is stripped).
// CHECK:      ^{{.*}}(%[[VAL2:.*]] : !riscv.reg, %[[ADDR2:.*]] : !riscv.reg):
// CHECK:      %[[ZADDR2:.*]] = "riscv.zextw"(%[[ADDR2]])
// CHECK:      "riscv.sw"(%[[VAL2]], %[[ZADDR2]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT: "func.return"() : () -> ()
