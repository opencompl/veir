// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %a = "riscv.li"() <{ value = 23 : i64 }> : () -> !reg
    %b = "riscv.sraiw"(%a) <{ value = 1 : i6 }> : (!reg) -> !reg
    %c = "riscv.li"() <{ value = 23 : i64 }> : () -> !reg
    %d = "riscv.sraiw"(%c) <{ value = -1 : i6 }> : (!reg) -> !reg
    "func.return"(%b, %d) : (!reg, !reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x000000000000000b#64, 0x0000000000000000#64]
