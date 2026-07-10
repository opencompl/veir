// RUN: veir-interpret %s | filecheck %s

// All four RISC-V stores target the same address, issued widest-to-narrowest so
// each narrower store overwrites only its low bytes and stays visible. Every
// source register holds the same byte replicated across all 8 lanes:
//   sd -> 0x04..04, sw -> 0x03..03, sh -> 0x02..02, sb -> 0x01..01

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !riscv.reg}> ({
    %a  = "riscv.li"() <{ "value" = 8 : i64 }> : () -> !riscv.reg
    %x8 = "riscv.li"() <{ "value" = 289360691352306692 : i64 }> : () -> !riscv.reg
    %x4 = "riscv.li"() <{ "value" = 217020518514230019 : i64 }> : () -> !riscv.reg
    %x2 = "riscv.li"() <{ "value" = 144680345676153346 : i64 }> : () -> !riscv.reg
    %x1 = "riscv.li"() <{ "value" = 72340172838076673 : i64 }> : () -> !riscv.reg
    "riscv.sd"(%x8, %a) <{ "value" = 0 : i64 }> : (!riscv.reg, !riscv.reg) -> ()
    "riscv.sw"(%x4, %a) <{ "value" = 0 : i64 }> : (!riscv.reg, !riscv.reg) -> ()
    "riscv.sh"(%x2, %a) <{ "value" = 0 : i64 }> : (!riscv.reg, !riscv.reg) -> ()
    "riscv.sb"(%x1, %a) <{ "value" = 0 : i64 }> : (!riscv.reg, !riscv.reg) -> ()
    %y = "riscv.ld"(%a) <{ "value" = 0 : i64 }> : (!riscv.reg) -> !riscv.reg
    "func.return"(%y) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0404040403030201#64]
