// RUN: veir-opt %s -p=riscv-combine,dce | filecheck %s

// `packh_high_bytes`: `or (slli (lbu b2), 16) (slli (lbu b3), 24) ->
// slli (packh b2 b3), 16`.
// `packh_high_bytes_commuted`: `or (slli (lbu b3), 24) (slli (lbu b2), 16) ->
// slli (packh b2 b3), 16`. A different shift amount must not match either rule.

"builtin.module"() ({
  "func.func"() <{function_type = (!riscv.reg) -> (!riscv.reg, !riscv.reg, !riscv.reg), sym_name = "packh_high_bytes"}> ({
  ^bb0(%addr: !riscv.reg):
    %b2 = "riscv.lbu"(%addr) <{"value" = 2 : i64}> : (!riscv.reg) -> !riscv.reg
    %b3 = "riscv.lbu"(%addr) <{"value" = 3 : i64}> : (!riscv.reg) -> !riscv.reg
    %s16 = "riscv.slli"(%b2) <{"value" = 16 : i64}> : (!riscv.reg) -> !riscv.reg
    %s24 = "riscv.slli"(%b3) <{"value" = 24 : i64}> : (!riscv.reg) -> !riscv.reg
    %packed = "riscv.or"(%s16, %s24) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s16_commuted = "riscv.slli"(%b2) <{"value" = 16 : i64}> : (!riscv.reg) -> !riscv.reg
    %s24_commuted = "riscv.slli"(%b3) <{"value" = 24 : i64}> : (!riscv.reg) -> !riscv.reg
    %packed_commuted = "riscv.or"(%s24_commuted, %s16_commuted) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %wrong_shift = "riscv.slli"(%b2) <{"value" = 17 : i64}> : (!riscv.reg) -> !riscv.reg
    %unchanged = "riscv.or"(%wrong_shift, %s24) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "func.return"(%packed, %packed_commuted, %unchanged) : (!riscv.reg, !riscv.reg, !riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: "sym_name" = "packh_high_bytes"
// CHECK: %[[B2:[^ ]*]] = "riscv.lbu"
// CHECK: %[[B3:[^ ]*]] = "riscv.lbu"
// CHECK: %[[PACKED:[^ ]*]] = "riscv.packh"(%[[B2]], %[[B3]])
// CHECK-NEXT: %[[HIGH:[^ ]*]] = "riscv.slli"(%[[PACKED]]) <{"value" = 16 : i64}>
// CHECK: %[[PACKED_COMMUTED:[^ ]*]] = "riscv.packh"(%[[B2]], %[[B3]])
// CHECK-NEXT: %[[HIGH_COMMUTED:[^ ]*]] = "riscv.slli"(%[[PACKED_COMMUTED]]) <{"value" = 16 : i64}>
// CHECK: %[[WRONG_SHIFT:[^ ]*]] = "riscv.slli"(%[[B2]]) <{"value" = 17 : i64}>
// CHECK-NEXT: %[[UNCHANGED:[^ ]*]] = "riscv.or"(%[[WRONG_SHIFT]], %{{.*}})
// CHECK: "func.return"(%[[HIGH]], %[[HIGH_COMMUTED]], %[[UNCHANGED]])
