// RUN: veir-interpret %s | filecheck %s

// `riscv.sw` stores the low word 0x80000000 at address 8; `riscv.lw`
// sign-extends the word to a full 64-bit register (the RV64 behavior), while
// `riscv.lwu` would zero-extend it.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !riscv.reg}> ({
    %a = "riscv.li"() <{ "value" = 8 : i64 }> : () -> !riscv.reg
    %x = "riscv.li"() <{ "value" = 2147483648 : i64 }> : () -> !riscv.reg
    "riscv.sw"(%x, %a) <{ "value" = 0 : i64 }> : (!riscv.reg, !riscv.reg) -> ()
    %y = "riscv.lw"(%a) <{ "value" = 0 : i64 }> : (!riscv.reg) -> !riscv.reg
    "func.return"(%y) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0xffffffff80000000#64]
