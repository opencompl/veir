// RUN: veir-interpret %s | filecheck %s

// `arith.mului_extended` returns the low and high halves of the 2w-bit unsigned
// product. 254 * 3 = 762 = 0x02fa: low = 0xfa, high = 0x02. The low half
// equals `arith.muli`.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i8)}> ({
    %c254 = "arith.constant"() <{ "value" = 254 : i8 }> : () -> i8
    %c3   = "arith.constant"() <{ "value" = 3 : i8 }> : () -> i8
    %lo, %hi = "arith.mului_extended"(%c254, %c3) : (i8, i8) -> (i8, i8)
    "func.return"(%lo, %hi) : (i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0xfa#8, 0x02#8]
