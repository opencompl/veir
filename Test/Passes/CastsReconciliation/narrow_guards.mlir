// RUN: veir-opt %s -p=reconcile-cast | filecheck %s

"builtin.module"() ({
  %x = "test.test"() : () -> !riscv.reg
  // CHECK: %[[X:.*]] = "test.test"() : () -> !riscv.reg

  // The smallest and largest widths that need two shifts.
  %i1 = "builtin.unrealized_conversion_cast"(%x) : (!riscv.reg) -> i1
  %r1 = "builtin.unrealized_conversion_cast"(%i1) : (i1) -> !riscv.reg
  // CHECK-NEXT: %[[L1:.*]] = "riscv.slli"(%[[X]]) <{"value" = 63 : i64}>
  // CHECK-NEXT: %[[R1:.*]] = "riscv.srli"(%[[L1]]) <{"value" = 63 : i64}>
  "test.test"(%r1) : (!riscv.reg) -> ()
  // CHECK-NEXT: "test.test"(%[[R1]])
  %i63 = "builtin.unrealized_conversion_cast"(%x) : (!riscv.reg) -> i63
  %r63 = "builtin.unrealized_conversion_cast"(%i63) : (i63) -> !riscv.reg
  // CHECK-NEXT: %[[L63:.*]] = "riscv.slli"(%[[X]]) <{"value" = 1 : i64}>
  // CHECK-NEXT: %[[R63:.*]] = "riscv.srli"(%[[L63]]) <{"value" = 1 : i64}>
  "test.test"(%r63) : (!riscv.reg) -> ()
  // CHECK-NEXT: "test.test"(%[[R63]])

  // A still-used inner cast survives reconciliation of its outer cast.
  %i8 = "builtin.unrealized_conversion_cast"(%x) : (!riscv.reg) -> i8
  %r8 = "builtin.unrealized_conversion_cast"(%i8) : (i8) -> !riscv.reg
  // CHECK-NEXT: %[[I8:.*]] = "builtin.unrealized_conversion_cast"(%[[X]]) : (!riscv.reg) -> i8
  // CHECK-NEXT: %[[R8:.*]] = "riscv.zextb"(%[[X]])
  "test.test"(%i8, %r8) : (i8, !riscv.reg) -> ()
  // CHECK-NEXT: "test.test"(%[[I8]], %[[R8]])

  // These patterns only rewrite round trips through an unallocated register.
  %a = "test.test"() : () -> !riscv.reg<x10>
  %ai = "builtin.unrealized_conversion_cast"(%a) : (!riscv.reg<x10>) -> i8
  %ar = "builtin.unrealized_conversion_cast"(%ai) : (i8) -> !riscv.reg<x10>
  // CHECK-NEXT: %[[A:.*]] = "test.test"() : () -> !riscv.reg<x10>
  // CHECK-NEXT: %[[AI:.*]] = "builtin.unrealized_conversion_cast"(%[[A]]) : (!riscv.reg<x10>) -> i8
  // CHECK-NEXT: %[[AR:.*]] = "builtin.unrealized_conversion_cast"(%[[AI]]) : (i8) -> !riscv.reg<x10>
  "test.test"(%ar) : (!riscv.reg<x10>) -> ()
  // CHECK-NEXT: "test.test"(%[[AR]])
}) : () -> ()
