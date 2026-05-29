// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %a = "riscv.li"() <{ value = 11 : i64 }> : () -> !reg
    %b = "riscv.srli"(%a) <{ value = 3 : i6 }> : (!reg) -> !reg
    %c = "riscv.li"() <{ value = 11 : i64 }> : () -> !reg
    %d = "riscv.srli"(%c) <{ value = -3 : i6 }> : (!reg) -> !reg
    "func.return"(%b, %d) : (!reg, !reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000001#64, 0x0000000000000000#64]
