// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %a = "riscv.li"() <{ value = 4294967298 : i64 }> : () -> !reg
    %b = "riscv.li"() <{ value = 2 : i64 }> : () -> !reg
    %c = "riscv.sh2adduw"(%a, %b) : (!reg, !reg) -> !reg
    "func.return"(%c) : (!reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x000000000000000a#64]
