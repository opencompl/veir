// RUN: veir-interpret %s | filecheck %s

// `arith.mulsi_extended` returns the low and high halves of the 2w-bit signed
// product. -2 * 3 = -6, represented in 16 bits as 0xfffa: low = 0xfa,
// high = 0xff. The low half equals `arith.muli`.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i8)}> ({
    %cn2 = "arith.constant"() <{ "value" = -2 : i8 }> : () -> i8
    %c3  = "arith.constant"() <{ "value" = 3 : i8 }> : () -> i8
    %lo, %hi = "arith.mulsi_extended"(%cn2, %c3) : (i8, i8) -> (i8, i8)
    "func.return"(%lo, %hi) : (i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0xfa#8, 0xff#8]
