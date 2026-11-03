// RUN: veir-interpret %s | filecheck %s

// Unsigned ceiling division: ceildivui(a, b) = a == 0 ? 0 : ((a-1)/b) + 1.
// 10 / 3 = 4, 12 / 5 = 3 (2.4 rounds up), 0 / 7 = 0, 8 / 2 = 4 (exact).
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i8, i8, i8)}> ({
    %c10 = "arith.constant"() <{ "value" = 10 : i8 }> : () -> i8
    %c12 = "arith.constant"() <{ "value" = 12 : i8 }> : () -> i8
    %c8  = "arith.constant"() <{ "value" = 8 : i8 }> : () -> i8
    %c0  = "arith.constant"() <{ "value" = 0 : i8 }> : () -> i8
    %c3  = "arith.constant"() <{ "value" = 3 : i8 }> : () -> i8
    %c5  = "arith.constant"() <{ "value" = 5 : i8 }> : () -> i8
    %c7  = "arith.constant"() <{ "value" = 7 : i8 }> : () -> i8
    %c2  = "arith.constant"() <{ "value" = 2 : i8 }> : () -> i8
    %r1 = "arith.ceildivui"(%c10, %c3) : (i8, i8) -> i8
    %r2 = "arith.ceildivui"(%c12, %c5) : (i8, i8) -> i8
    %r3 = "arith.ceildivui"(%c0, %c7) : (i8, i8) -> i8
    %r4 = "arith.ceildivui"(%c8, %c2) : (i8, i8) -> i8
    "func.return"(%r1, %r2, %r3, %r4) : (i8, i8, i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x04#8, 0x03#8, 0x00#8, 0x04#8]
