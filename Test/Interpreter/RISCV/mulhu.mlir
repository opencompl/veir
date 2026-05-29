// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %a = "riscv.li"() <{ value = 2 : i64 }> : () -> !reg
    %b = "riscv.li"() <{ value = 5 : i64 }> : () -> !reg
    %c = "riscv.li"() <{ value = -5 : i64 }> : () -> !reg
    %d = "riscv.li"() <{ value = -4294967288 : i64 }> : () -> !reg
    %e = "riscv.li"() <{ value = 3 : i64 }> : () -> !reg
    %f = "riscv.mulhu"(%a, %b) : (!reg, !reg) -> !reg
    %g = "riscv.mulhu"(%a, %c) : (!reg, !reg) -> !reg
    %h = "riscv.mulhu"(%d, %e) : (!reg, !reg) -> !reg
    "func.return"(%f, %g, %h) : (!reg, !reg, !reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000000#64, 0x0000000000000001#64, 0x0000000000000002#64]
