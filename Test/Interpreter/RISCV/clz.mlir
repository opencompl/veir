// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %a = "riscv.li"() <{ value = 2 : i64 }> : () -> !reg
    %b = "riscv.li"() <{ value = -5 : i64 }> : () -> !reg
    %c = "riscv.li"() <{ value = 4294967297 : i64 }> : () -> !reg
    %d = "riscv.clz"(%a) : (!reg) -> !reg
    %e = "riscv.clz"(%b) : (!reg) -> !reg
    %f = "riscv.clz"(%c) : (!reg) -> !reg
    "func.return"(%d, %e, %f) : (!reg, !reg, !reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x000000000000003e#64, 0x0000000000000000#64, 0x000000000000001f#64]
