// RUN: veir-interpret %s | filecheck %s

// `arith.addui_extended` returns the w-bit sum and an i1 unsigned-overflow flag.
// 200 + 100 = 300 -> sum 0x2c, overflow 1.
// 100 + 100 = 200 -> sum 0xc8, overflow 0.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i1, i8, i1)}> ({
    %c200 = "arith.constant"() <{ "value" = 200 : i8 }> : () -> i8
    %c100 = "arith.constant"() <{ "value" = 100 : i8 }> : () -> i8
    %s1, %o1 = "arith.addui_extended"(%c200, %c100) : (i8, i8) -> (i8, i1)
    %s2, %o2 = "arith.addui_extended"(%c100, %c100) : (i8, i8) -> (i8, i1)
    "func.return"(%s1, %o1, %s2, %o2) : (i8, i1, i8, i1) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x2c#8, 0x1#1, 0xc8#8, 0x0#1]
