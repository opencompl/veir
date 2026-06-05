// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    ^1():
      %x = "riscv.li"() <{ "value" = 9 : i64 }> : () -> !riscv.reg
      "riscv_cf.branch"(%x) [^2] : (!riscv.reg) -> ()
    ^2(%y : !riscv.reg):
      "func.return"(%y) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000009#64]
