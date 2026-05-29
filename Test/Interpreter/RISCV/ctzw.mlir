// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %a = "riscv.li"() <{ value = 2 : i64 }> : () -> !reg
    %b = "riscv.li"() <{ value = -5 : i64 }> : () -> !reg
    %c = "riscv.ctzw"(%a) : (!reg) -> !reg
    %d = "riscv.ctzw"(%b) : (!reg) -> !reg
    "func.return"(%c, %d) : (!reg, !reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000001#64, 0x0000000000000000#64]
