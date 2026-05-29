// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %a = "riscv.li"() <{ value = 2 : i64 }> : () -> !reg
    %b = "riscv.li"() <{ value = 5 : i64 }> : () -> !reg
    %c = "riscv.li"() <{ value = -5 : i64 }> : () -> !reg
    %d = "riscv.li"() <{ value = 4294967298 : i64 }> : () -> !reg
    %f = "riscv.sh2add"(%a, %b) : (!reg, !reg) -> !reg
    %g = "riscv.sh2add"(%a, %c) : (!reg, !reg) -> !reg
    %h = "riscv.sh2add"(%d, %a) : (!reg, !reg) -> !reg
    "func.return"(%f, %g, %h) : (!reg, !reg, !reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x000000000000000d#64, 0x0000000000000003#64, 0x000000040000000a#64]
