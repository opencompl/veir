// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    ^1():
      %x = "riscv.li"() <{ "value" = 9 : i64 }> : () -> !reg
      "riscv_cf.branch"(%x) [^2] : (!reg) -> ()
    ^2(%y : !reg):
      "func.return"(%y) : (!reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000009#64]
