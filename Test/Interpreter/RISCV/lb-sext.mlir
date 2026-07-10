// RUN: veir-interpret %s | filecheck %s

// `riscv.sb` stores the low byte 0xFF at address 8; `riscv.lb` sign-extends the
// byte to a full 64-bit register.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !riscv.reg}> ({
    %a = "riscv.li"() <{ "value" = 8 : i64 }> : () -> !riscv.reg
    %x = "riscv.li"() <{ "value" = 255 : i64 }> : () -> !riscv.reg
    "riscv.sb"(%x, %a) <{ "value" = 0 : i64 }> : (!riscv.reg, !riscv.reg) -> ()
    %y = "riscv.lb"(%a) <{ "value" = 0 : i64 }> : (!riscv.reg) -> !riscv.reg
    "func.return"(%y) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0xffffffffffffffff#64]
