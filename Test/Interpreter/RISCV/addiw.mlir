// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %a = "riscv.li"() <{ value = 2 : i64 }> : () -> !reg
    %b = "riscv.addiw"(%a) <{ value = 3 : i12 }> : (!reg) -> !reg
    %c = "riscv.li"() <{ value = 2 : i64 }> : () -> !reg
    %d = "riscv.addiw"(%c) <{ value = -31 : i12 }> : (!reg) -> !reg
    "func.return"(%b, %d) : (!reg, !reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000005#64, 0xffffffffffffffe3#64]
