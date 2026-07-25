// RUN: veir-interpret %s | filecheck %s

// Signed floor division (rounds toward -infinity).
//  7 /  2 =  3 (0x03)      -7 /  2 = -4 (0xfc)
//  7 / -2 = -4 (0xfc)      -7 / -2 =  3 (0x03)
// -6 /  2 = -3 (exact, 0xfd)
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i8, i8, i8, i8)}> ({
    %c7  = "arith.constant"() <{ "value" = 7 : i8 }> : () -> i8
    %cn7 = "arith.constant"() <{ "value" = -7 : i8 }> : () -> i8
    %cn6 = "arith.constant"() <{ "value" = -6 : i8 }> : () -> i8
    %c2  = "arith.constant"() <{ "value" = 2 : i8 }> : () -> i8
    %cn2 = "arith.constant"() <{ "value" = -2 : i8 }> : () -> i8
    %r1 = "arith.floordivsi"(%c7, %c2) : (i8, i8) -> i8
    %r2 = "arith.floordivsi"(%cn7, %c2) : (i8, i8) -> i8
    %r3 = "arith.floordivsi"(%c7, %cn2) : (i8, i8) -> i8
    %r4 = "arith.floordivsi"(%cn7, %cn2) : (i8, i8) -> i8
    %r5 = "arith.floordivsi"(%cn6, %c2) : (i8, i8) -> i8
    "func.return"(%r1, %r2, %r3, %r4, %r5) : (i8, i8, i8, i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x03#8, 0xfc#8, 0xfc#8, 0x03#8, 0xfd#8]
