// RUN: veir-interpret %s | filecheck %s

// `riscv.sh` stores the low halfword 0x8000 at address 8; `riscv.lh`
// sign-extends the halfword to a full 64-bit register, while `riscv.lhu` would
// zero-extend it.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !riscv.reg}> ({
    %a = "riscv.li"() <{ "value" = 8 : i64 }> : () -> !riscv.reg
    %x = "riscv.li"() <{ "value" = 32768 : i64 }> : () -> !riscv.reg
    "riscv.sh"(%a, %x) <{ "value" = 0 : i64 }> : (!riscv.reg, !riscv.reg) -> ()
    %y = "riscv.lh"(%a) <{ "value" = 0 : i64 }> : (!riscv.reg) -> !riscv.reg
    "func.return"(%y) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0xffffffffffff8000#64]
