// RUN: veir-interpret %s | filecheck %s

// 384 = 0x180: trunc to i8 gives 0x80 = 128
//   nsw: sext(0x80) = -128 != 384, poison
//   nuw: zext(0x80) = 128 != 384, poison
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i8, i8, i8)}> ({
    %c384 = "arith.constant"() <{ "value" = 384 : i32 }> : () -> i32
    %none    = "arith.trunci"(%c384) : (i32) -> i8
    %nsw     = "arith.trunci"(%c384) <{"overflowFlags" = 1 : i32}> : (i32) -> i8
    %nuw     = "arith.trunci"(%c384) <{"overflowFlags" = 2 : i32}> : (i32) -> i8
    %nuw_nsw = "arith.trunci"(%c384) <{"overflowFlags" = 3 : i32}> : (i32) -> i8
    "func.return"(%none, %nsw, %nuw, %nuw_nsw) : (i8, i8, i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x80#8, poison, poison, poison]
