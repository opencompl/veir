// RUN: veir-interpret %s | filecheck %s

// Store the byte values 124..131 at byte addresses 124..131 using a single
// `riscv.sd` (the little-endian doubleword 0x838281807f7e7d7c places 124 at the
// lowest address and 131 at the highest). Then `riscv.lb` each of those 8 bytes,
// which sign-extends: 124..127 stay positive, 128..131 become -128..-125. The
// sum is (124+125+126+127) + (-128-127-126-125) = -4.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !riscv.reg}> ({
    %base = "riscv.li"() <{ "value" = 124 : i64 }> : () -> !riscv.reg
    %word = "riscv.li"() <{ "value" = 9476278954835737980 : i64 }> : () -> !riscv.reg
    "riscv.sd"(%word, %base) <{ "value" = 0 : i64 }> : (!riscv.reg, !riscv.reg) -> ()

    %b0 = "riscv.lb"(%base) <{ "value" = 0 : i64 }> : (!riscv.reg) -> !riscv.reg
    %b1 = "riscv.lb"(%base) <{ "value" = 1 : i64 }> : (!riscv.reg) -> !riscv.reg
    %b2 = "riscv.lb"(%base) <{ "value" = 2 : i64 }> : (!riscv.reg) -> !riscv.reg
    %b3 = "riscv.lb"(%base) <{ "value" = 3 : i64 }> : (!riscv.reg) -> !riscv.reg
    %b4 = "riscv.lb"(%base) <{ "value" = 4 : i64 }> : (!riscv.reg) -> !riscv.reg
    %b5 = "riscv.lb"(%base) <{ "value" = 5 : i64 }> : (!riscv.reg) -> !riscv.reg
    %b6 = "riscv.lb"(%base) <{ "value" = 6 : i64 }> : (!riscv.reg) -> !riscv.reg
    %b7 = "riscv.lb"(%base) <{ "value" = 7 : i64 }> : (!riscv.reg) -> !riscv.reg

    %s0 = "riscv.add"(%b0, %b1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s1 = "riscv.add"(%s0, %b2) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s2 = "riscv.add"(%s1, %b3) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s3 = "riscv.add"(%s2, %b4) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s4 = "riscv.add"(%s3, %b5) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s5 = "riscv.add"(%s4, %b6) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %sum = "riscv.add"(%s5, %b7) : (!riscv.reg, !riscv.reg) -> !riscv.reg

    "func.return"(%sum) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0xfffffffffffffffc#64]
