// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %a = "riscv.li"() <{ value = 23 : i64 }> : () -> !reg
    %b = "riscv.andi"(%a) <{ value = 3 : i12 }> : (!reg) -> !reg
    %c = "riscv.li"() <{ value = 23 : i64 }> : () -> !reg
    %d = "riscv.andi"(%c) <{ value = -3 : i12 }> : (!reg) -> !reg
    "func.return"(%b, %d) : (!reg, !reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000003#64, 0x0000000000000015#64]
