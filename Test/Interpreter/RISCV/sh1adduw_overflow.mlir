// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %a = "riscv.li"() <{ value = 4294967298 : i64 }> : () -> !reg
    %b = "riscv.li"() <{ value = 2 : i64 }> : () -> !reg
    %c = "riscv.sh1adduw"(%a, %b) : (!reg, !reg) -> !reg
    "func.return"(%c) : (!reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000006#64]
