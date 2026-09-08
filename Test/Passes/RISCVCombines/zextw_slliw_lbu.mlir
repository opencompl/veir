// RUN: veir-opt %s -p=riscv-combine,dce | filecheck %s

// Full-width shifts are equivalent to `zextw(slliw(lbu))` for the byte-packing
// shift amounts 8, 16, and 24. Nearby amounts must remain untouched.

"builtin.module"() ({
  "func.func"() <{function_type = (!riscv.reg) -> (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg), sym_name = "zextw_slliw_lbu"}> ({
  ^bb0(%addr: !riscv.reg):
    %byte = "riscv.lbu"(%addr) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
    %s8 = "riscv.slliw"(%byte) <{"value" = 8 : i64}> : (!riscv.reg) -> !riscv.reg
    %z8 = "riscv.zextw"(%s8) : (!riscv.reg) -> !riscv.reg
    %s16 = "riscv.slliw"(%byte) <{"value" = 16 : i64}> : (!riscv.reg) -> !riscv.reg
    %z16 = "riscv.zextw"(%s16) : (!riscv.reg) -> !riscv.reg
    %s24 = "riscv.slliw"(%byte) <{"value" = 24 : i64}> : (!riscv.reg) -> !riscv.reg
    %z24 = "riscv.zextw"(%s24) : (!riscv.reg) -> !riscv.reg
    %s7 = "riscv.slliw"(%byte) <{"value" = 7 : i64}> : (!riscv.reg) -> !riscv.reg
    %z7 = "riscv.zextw"(%s7) : (!riscv.reg) -> !riscv.reg
    "func.return"(%z8, %z16, %z24, %z7) : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: "sym_name" = "zextw_slliw_lbu"
// CHECK: %[[BYTE:[^ ]*]] = "riscv.lbu"
// CHECK: %[[SHIFT8:[^ ]*]] = "riscv.slli"(%[[BYTE]]) <{"value" = 8 : i64}>
// CHECK: %[[SHIFT16:[^ ]*]] = "riscv.slli"(%[[BYTE]]) <{"value" = 16 : i64}>
// CHECK: %[[SHIFT24:[^ ]*]] = "riscv.slli"(%[[BYTE]]) <{"value" = 24 : i64}>
// CHECK: %[[SHIFT7:[^ ]*]] = "riscv.slliw"(%[[BYTE]]) <{"value" = 7 : i64}>
// CHECK-NEXT: %[[ZSHIFT7:[^ ]*]] = "riscv.zextw"(%[[SHIFT7]])
// CHECK: "func.return"(%[[SHIFT8]], %[[SHIFT16]], %[[SHIFT24]], %[[ZSHIFT7]])
