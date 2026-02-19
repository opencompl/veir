// RUN: veir-opt %s | filecheck %s

"builtin.module"() ({
^bb0():
  %5 = "arith.constant"() <{ "value" = 13 : i32 }> : () -> i32
  %6 = "arith.addi"(%5, %5) : (i32, i32) -> i32
  %7 = "arith.subi"(%5, %5) : (i32, i32) -> i32
  %8 = "arith.muli"(%5, %5) : (i32, i32) -> i32
  %9 = "arith.andi"(%5, %5) : (i32, i32) -> i32
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT: ^4():
// CHECK-NEXT:    %5 = "arith.constant"() <{ "value" = 13 : i32 }> : () -> i32
// CHECK-NEXT:    %6 = "arith.addi"(%5, %5) : (i32, i32) -> i32
// CHECK-NEXT:    %7 = "arith.subi"(%5, %5) : (i32, i32) -> i32
// CHECK-NEXT:    %8 = "arith.muli"(%5, %5) : (i32, i32) -> i32
// CHECK-NEXT:    %9 = "arith.andi"(%5, %5) : (i32, i32) -> i32
// CHECK-NEXT: }) : () -> ()
