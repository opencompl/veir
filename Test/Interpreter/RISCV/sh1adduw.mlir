// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %a = "riscv.li"() <{ value = 2 : i64 }> : () -> !reg
    %b = "riscv.li"() <{ value = 5 : i64 }> : () -> !reg
    %c = "riscv.li"() <{ value = -5 : i64 }> : () -> !reg
    %d = "riscv.sh1adduw"(%a, %b) : (!reg, !reg) -> !reg
    %e = "riscv.sh1adduw"(%a, %c) : (!reg, !reg) -> !reg
    "func.return"(%d, %e) : (!reg, !reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000009#64, 0xffffffffffffffff#64]
