// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !riscv.reg}> ({
    %a  = "riscv.li"() <{ "value" = 8 : i64 }> : () -> !riscv.reg
    %x8 = "riscv.li"() <{ "value" = 289360691352306692 : i64 }> : () -> !riscv.reg
    %x4 = "riscv.li"() <{ "value" = 217020518514230019 : i64 }> : () -> !riscv.reg
    %x2 = "riscv.li"() <{ "value" = 144680345676153346 : i64 }> : () -> !riscv.reg
    %x1 = "riscv.li"() <{ "value" = 72340172838076673 : i64 }> : () -> !riscv.reg
    "riscv.sd"(%x8, %a) <{ "value" = 0 : i64 }> : (!riscv.reg, !riscv.reg) -> ()
    "riscv.sw"(%x4, %a) <{ "value" = 4 : i64 }> : (!riscv.reg, !riscv.reg) -> ()
    "riscv.sh"(%x2, %a) <{ "value" = 6 : i64 }> : (!riscv.reg, !riscv.reg) -> ()
    "riscv.sb"(%x1, %a) <{ "value" = 7 : i64 }> : (!riscv.reg, !riscv.reg) -> ()
    %y = "riscv.ld"(%a) <{ "value" = 0 : i64 }> : (!riscv.reg) -> !riscv.reg
    "func.return"(%y) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0102030304040404#64]
