// RUN: veir-opt %s | filecheck %s

"builtin.module"() ({
^bb0():
  %0 = "mod_arith.constant"() <{ "value" = 13 : i32 }> : () -> i32
  %1 = "mod_arith.constant"() <{ "value" = 7 : i32 }> : () -> i32
  %2 = "mod_arith.add"(%0, %1) : (i32, i32) -> i32
  %3 = "mod_arith.barrett_reduce"(%2) : (i32) -> i32
  %4 = "mod_arith.encapsulate"(%0) : (i32) -> i32
  %5 = "mod_arith.extract"(%4) : (i32) -> i32
  %6 = "mod_arith.mac"(%0, %1, %2) : (i32, i32, i32) -> i32
  %7 = "mod_arith.mod_switch"(%6) : (i32) -> i32
  %8 = "mod_arith.mul"(%0, %1) : (i32, i32) -> i32
  %9 = "mod_arith.reduce"(%8) : (i32) -> i32
  %10 = "mod_arith.subifge"(%0, %1) : (i32, i32) -> i32
  %11 = "mod_arith.sub"(%0, %1) : (i32, i32) -> i32
}) : () -> ()

// CHECK:       "builtin.module"() ({
// CHECK-NEXT:   ^4():
// CHECK-NEXT:     %5 = "mod_arith.constant"() <{ "value" = 13 : i32 }> : () -> i32
// CHECK-NEXT:     %6 = "mod_arith.constant"() <{ "value" = 7 : i32 }> : () -> i32
// CHECK-NEXT:     %7 = "mod_arith.add"(%5, %6) : (i32, i32) -> i32
// CHECK-NEXT:     %8 = "mod_arith.barrett_reduce"(%7) : (i32) -> i32
// CHECK-NEXT:     %9 = "mod_arith.encapsulate"(%5) : (i32) -> i32
// CHECK-NEXT:     %10 = "mod_arith.extract"(%9) : (i32) -> i32
// CHECK-NEXT:     %11 = "mod_arith.mac"(%5, %6, %7) : (i32, i32, i32) -> i32
// CHECK-NEXT:     %12 = "mod_arith.mod_switch"(%11) : (i32) -> i32
// CHECK-NEXT:     %13 = "mod_arith.mul"(%5, %6) : (i32, i32) -> i32
// CHECK-NEXT:     %14 = "mod_arith.reduce"(%13) : (i32) -> i32
// CHECK-NEXT:     %15 = "mod_arith.subifge"(%5, %6) : (i32, i32) -> i32
// CHECK-NEXT:     %16 = "mod_arith.sub"(%5, %6) : (i32, i32) -> i32
// CHECK-NEXT: }) : () -> ()
