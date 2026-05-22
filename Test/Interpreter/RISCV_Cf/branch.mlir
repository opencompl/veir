// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  ^1():
    %x = "riscv.li"() <{ "value" = 9 : i64 }> : () -> i64
    "riscv_cf.branch"(%x) [^2] : (i64) -> ()
  ^2(%y : i64):
    "func.return"(%y) : (i64) -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000009#64]
