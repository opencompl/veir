// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `riscv.srli 63 (riscv.slli 63 X) -> X` when `X` is a comparison op that's
// already guaranteed to produce exactly 0 or 1: `slli 63` isolates bit 0 into
// bit 63, and `srli 63` moves it straight back -- an identity for such `X`.

"builtin.module"() ({
  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> !riscv.reg, sym_name = "f0"}> ({
  ^bb0(%x: !riscv.reg, %y: !riscv.reg):
    %c = "riscv.sltu"(%x, %y) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s = "riscv.slli"(%c) <{"value" = 63 : i64}> : (!riscv.reg) -> !riscv.reg
    %r = "riscv.srli"(%s) <{"value" = 63 : i64}> : (!riscv.reg) -> !riscv.reg
    "func.return"(%r) : (!riscv.reg) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> !riscv.reg, sym_name = "f1"}> ({
  ^bb0(%x: !riscv.reg, %y: !riscv.reg):
    %c = "riscv.slt"(%x, %y) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s = "riscv.slli"(%c) <{"value" = 63 : i64}> : (!riscv.reg) -> !riscv.reg
    %r = "riscv.srli"(%s) <{"value" = 63 : i64}> : (!riscv.reg) -> !riscv.reg
    "func.return"(%r) : (!riscv.reg) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (!riscv.reg) -> !riscv.reg, sym_name = "f2"}> ({
  ^bb0(%x: !riscv.reg):
    %c = "riscv.sltiu"(%x) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
    %s = "riscv.slli"(%c) <{"value" = 63 : i64}> : (!riscv.reg) -> !riscv.reg
    %r = "riscv.srli"(%s) <{"value" = 63 : i64}> : (!riscv.reg) -> !riscv.reg
    "func.return"(%r) : (!riscv.reg) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (!riscv.reg) -> !riscv.reg, sym_name = "f3"}> ({
  ^bb0(%x: !riscv.reg):
    %c = "riscv.seqz"(%x) : (!riscv.reg) -> !riscv.reg
    %s = "riscv.slli"(%c) <{"value" = 63 : i64}> : (!riscv.reg) -> !riscv.reg
    %r = "riscv.srli"(%s) <{"value" = 63 : i64}> : (!riscv.reg) -> !riscv.reg
    "func.return"(%r) : (!riscv.reg) -> ()
  }) : () -> ()

  // Negative case: the shifted value isn't known to be 0/1 (it's an ordinary
  // `add`), so the shift pair must stay.
  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> !riscv.reg, sym_name = "f4"}> ({
  ^bb0(%x: !riscv.reg, %y: !riscv.reg):
    %c = "riscv.add"(%x, %y) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s = "riscv.slli"(%c) <{"value" = 63 : i64}> : (!riscv.reg) -> !riscv.reg
    %r = "riscv.srli"(%s) <{"value" = 63 : i64}> : (!riscv.reg) -> !riscv.reg
    "func.return"(%r) : (!riscv.reg) -> ()
  }) : () -> ()

  // Negative case: wrong shift amount (not width-1) must not be touched.
  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> !riscv.reg, sym_name = "f5"}> ({
  ^bb0(%x: !riscv.reg, %y: !riscv.reg):
    %c = "riscv.sltu"(%x, %y) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s = "riscv.slli"(%c) <{"value" = 62 : i64}> : (!riscv.reg) -> !riscv.reg
    %r = "riscv.srli"(%s) <{"value" = 63 : i64}> : (!riscv.reg) -> !riscv.reg
    "func.return"(%r) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// riscv-combine alone (no dce) leaves the now-dead `slli` in place; what
// matters is that `func.return` no longer reads through the shift pair.
// CHECK:      %[[SLTU:.*]] = "riscv.sltu"(%{{.*}}, %{{.*}})
// CHECK:      "func.return"(%[[SLTU]]) : (!riscv.reg) -> ()

// CHECK:      %[[SLT:.*]] = "riscv.slt"(%{{.*}}, %{{.*}})
// CHECK:      "func.return"(%[[SLT]]) : (!riscv.reg) -> ()

// CHECK:      %[[SLTIU:.*]] = "riscv.sltiu"(%{{.*}}) <{"value" = 1 : i64}>
// CHECK:      "func.return"(%[[SLTIU]]) : (!riscv.reg) -> ()

// CHECK:      %[[SEQZ:.*]] = "riscv.seqz"(%{{.*}})
// CHECK:      "func.return"(%[[SEQZ]]) : (!riscv.reg) -> ()

// CHECK:      %[[ADD:.*]] = "riscv.add"(%{{.*}}, %{{.*}})
// CHECK-NEXT: %[[ADD_SLLI:.*]] = "riscv.slli"(%[[ADD]]) <{"value" = 63 : i64}>
// CHECK-NEXT: %[[ADD_SRLI:.*]] = "riscv.srli"(%[[ADD_SLLI]]) <{"value" = 63 : i64}>
// CHECK-NEXT: "func.return"(%[[ADD_SRLI]]) : (!riscv.reg) -> ()

// CHECK:      %[[WRONG:.*]] = "riscv.sltu"(%{{.*}}, %{{.*}})
// CHECK-NEXT: %[[WRONG_SLLI:.*]] = "riscv.slli"(%[[WRONG]]) <{"value" = 62 : i64}>
// CHECK-NEXT: %[[WRONG_SRLI:.*]] = "riscv.srli"(%[[WRONG_SLLI]]) <{"value" = 63 : i64}>
// CHECK-NEXT: "func.return"(%[[WRONG_SRLI]]) : (!riscv.reg) -> ()
