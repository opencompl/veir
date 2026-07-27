// RUN: veir-interpret %s | filecheck %s

// `arith.subui_extended` returns the w-bit difference and an i1 borrow flag,
// which is set exactly when the subtraction underflows, i.e. lhs <u rhs.
//   100 - 200 = -100 -> diff 0x9c, borrow 1.
//   200 - 100 =  100 -> diff 0x64, borrow 0.
//   100 - 100 =    0 -> diff 0x00, borrow 0.
//   0   - 1         -> diff 0xff, borrow 1.
// 200 is 0xc8, so as a signed i8 it is negative; the borrow is unsigned, so
// 200 - 100 does not borrow even though the signed difference would.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i1, i8, i1, i8, i1, i8, i1)}> ({
    %c0 = "arith.constant"() <{ "value" = 0 : i8 }> : () -> i8
    %c1 = "arith.constant"() <{ "value" = 1 : i8 }> : () -> i8
    %c100 = "arith.constant"() <{ "value" = 100 : i8 }> : () -> i8
    %c200 = "arith.constant"() <{ "value" = 200 : i8 }> : () -> i8
    %d1, %b1 = "arith.subui_extended"(%c100, %c200) : (i8, i8) -> (i8, i1)
    %d2, %b2 = "arith.subui_extended"(%c200, %c100) : (i8, i8) -> (i8, i1)
    %d3, %b3 = "arith.subui_extended"(%c100, %c100) : (i8, i8) -> (i8, i1)
    %d4, %b4 = "arith.subui_extended"(%c0, %c1) : (i8, i8) -> (i8, i1)
    "func.return"(%d1, %b1, %d2, %b2, %d3, %b3, %d4, %b4)
      : (i8, i1, i8, i1, i8, i1, i8, i1) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x9c#8, 0x1#1, 0x64#8, 0x0#1, 0x00#8, 0x0#1, 0xff#8, 0x1#1]
