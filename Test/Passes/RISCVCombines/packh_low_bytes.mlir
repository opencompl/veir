// RUN: veir-opt %s -p=riscv-combine,dce | filecheck %s

// Pack two adjacent zero-extended bytes. Both OR operand orders are valid;
// a different shift amount is not.

"builtin.module"() ({
  "func.func"() <{function_type = (!riscv.reg) -> (!riscv.reg, !riscv.reg, !riscv.reg), sym_name = "packh_low_bytes"}> ({
  ^bb0(%addr: !riscv.reg):
    %lo = "riscv.lbu"(%addr) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
    %hi = "riscv.lbu"(%addr) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
    %shifted = "riscv.slli"(%hi) <{"value" = 8 : i64}> : (!riscv.reg) -> !riscv.reg
    %packed = "riscv.or"(%lo, %shifted) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %shifted_commuted = "riscv.slli"(%hi) <{"value" = 8 : i64}> : (!riscv.reg) -> !riscv.reg
    %packed_commuted = "riscv.or"(%shifted_commuted, %lo) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %wrong_shift = "riscv.slli"(%hi) <{"value" = 9 : i64}> : (!riscv.reg) -> !riscv.reg
    %unchanged = "riscv.or"(%lo, %wrong_shift) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "func.return"(%packed, %packed_commuted, %unchanged) : (!riscv.reg, !riscv.reg, !riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: "sym_name" = "packh_low_bytes"
// CHECK: %[[LO:[^ ]*]] = "riscv.lbu"
// CHECK: %[[HI:[^ ]*]] = "riscv.lbu"
// CHECK: %[[PACKED:[^ ]*]] = "riscv.packh"(%[[LO]], %[[HI]])
// CHECK: %[[PACKED_COMMUTED:[^ ]*]] = "riscv.packh"(%[[LO]], %[[HI]])
// CHECK: %[[WRONG_SHIFT:[^ ]*]] = "riscv.slli"(%[[HI]]) <{"value" = 9 : i64}>
// CHECK-NEXT: %[[UNCHANGED:[^ ]*]] = "riscv.or"(%[[LO]], %[[WRONG_SHIFT]])
// CHECK: "func.return"(%[[PACKED]], %[[PACKED_COMMUTED]], %[[UNCHANGED]])
