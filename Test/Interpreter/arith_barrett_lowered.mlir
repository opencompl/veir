// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %arg = "arith.constant"() <{ "value" = 23 : i10 }> : () -> i10
  %0 = "arith.constant"() <{ "value" = 60 : i15 }> : () -> i15
  %1 = "arith.constant"() <{ "value" = 10 : i15 }> : () -> i15
  %2 = "arith.constant"() <{ "value" = 17 : i15 }> : () -> i15
  %3 = "arith.extui"(%arg) : (i10) -> i15
  %4 = "arith.muli"(%3, %0) : (i15, i15) -> i15
  %5 = "arith.shrui"(%4, %1) : (i15, i15) -> i15
  %6 = "arith.muli"(%5, %2) : (i15, i15) -> i15
  %7 = "arith.subi"(%3, %6) : (i15, i15) -> i15
  %8 = "arith.trunci"(%7) : (i15) -> i10
  "func.return"(%8) : (i10) -> ()
}) : () -> ()

// CHECK: Program output: #[0x006#10]
