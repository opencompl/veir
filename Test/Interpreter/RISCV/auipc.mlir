// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %a = "riscv.li"() <{ value = 2 : i64 }> : () -> !reg
    %b = "riscv.auipc"(%a) <{ value = 3 : i20 }> : (!reg) -> !reg
    %c = "riscv.li"() <{ value = 2 : i64 }> : () -> !reg
    %d = "riscv.auipc"(%c) <{ value = -3 : i20 }> : (!reg) -> !reg
    "func.return"(%b, %d) : (!reg, !reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000003002#64, 0xffffffffffffd002#64]
