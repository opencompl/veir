// RUN: veir-interpret %s | filecheck %s

// Initialize memory bytes 0..15 so that each byte contains its own address,
// using two doubleword stores (little-endian):
//   sd @0 = 0x0706050403020100  -> bytes 0..7  = 00 01 02 03 04 05 06 07
//   sd @8 = 0x0F0E0D0C0B0A0908  -> bytes 8..15 = 08 09 0A 0B 0C 0D 0E 0F
// Then a misaligned doubleword load from address 3 reads bytes 3..10:
//   03 04 05 06 07 08 09 0A, which little-endian is 0x0a09080706050403.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !riscv.reg}> ({
    %a0 = "riscv.li"() <{ "value" = 0 : i64 }> : () -> !riscv.reg
    %v0 = "riscv.li"() <{ "value" = 506097522914230528 : i64 }> : () -> !riscv.reg
    "riscv.sd"(%a0, %v0) <{ "value" = 0 : i64 }> : (!riscv.reg, !riscv.reg) -> ()

    %a8 = "riscv.li"() <{ "value" = 8 : i64 }> : () -> !riscv.reg
    %v8 = "riscv.li"() <{ "value" = 1084818905618843912 : i64 }> : () -> !riscv.reg
    "riscv.sd"(%a8, %v8) <{ "value" = 0 : i64 }> : (!riscv.reg, !riscv.reg) -> ()

    %y = "riscv.ld"(%a8) <{ "value" = -5 : i64 }> : (!riscv.reg) -> !riscv.reg
    "func.return"(%y) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0a09080706050403#64]
