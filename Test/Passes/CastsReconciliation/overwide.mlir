// RUN: not veir-opt %s -p=reconcile-cast 2>&1 | filecheck %s

// Preserve the reconciliation pass's error for an over-wide register round trip.
// CHECK: Error while applying cast reconciliation
"builtin.module"() ({
  %x = "test.test"() : () -> !riscv.reg
  %i = "builtin.unrealized_conversion_cast"(%x) : (!riscv.reg) -> i65
  %r = "builtin.unrealized_conversion_cast"(%i) : (i65) -> !riscv.reg
  "test.test"(%r) : (!riscv.reg) -> ()
}) : () -> ()
