// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %a = "riscv.li"() <{ value = 29 : i64 }> : () -> !reg
    %b = "riscv.ori"(%a) <{ value = 3 : i12 }> : (!reg) -> !reg
    %c = "riscv.li"() <{ value = 29 : i64 }> : () -> !reg
    %d = "riscv.ori"(%c) <{ value = -3 : i12 }> : (!reg) -> !reg
    "func.return"(%b, %d) : (!reg, !reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x000000000000001f#64, 0xfffffffffffffffd#64]
