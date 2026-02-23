// RUN: veir-opt %s | filecheck %s

"builtin.module"() ({
^4():
  %5 = "arith.constant"() <{ "value" = 13 : i32 }> : () -> i32
  %6 = "arith.addi"(%5, %5) : (i32, i32) -> i32
  %70, %71 = "arith.addui_extended"(%5, %5) : (i32, i32) -> (i32, i32)
  %8 = "arith.andi"(%5, %5) : (i32, i32) -> i32
  %9 = "arith.ceildivsi"(%5, %5) : (i32, i32) -> i32
  %10 = "arith.ceildivui"(%5, %5) : (i32, i32) -> i32
  %11 = "arith.cmpi"(%5, %5) : (i32, i32) -> i1
  %12 = "arith.divsi"(%5, %5) : (i32, i32) -> i32
  %13 = "arith.divui"(%5, %5) : (i32, i32) -> i32
  %14 = "arith.extui"(%5) : (i32) -> i32
  %15 = "arith.floordivsi"(%5, %5) : (i32, i32) -> i32
  %16 = "arith.maxsi"(%5, %5) : (i32, i32) -> i32
  %17 = "arith.maxui"(%5, %5) : (i32, i32) -> i32
  %18 = "arith.minsi"(%5, %5) : (i32, i32) -> i32
  %19 = "arith.minui"(%5, %5) : (i32, i32) -> i32
  %20 = "arith.muli"(%5, %5) : (i32, i32) -> i32
  %210, %211 = "arith.mulsi_extended"(%5, %5) : (i32, i32) -> (i32, i32)
  %220, %221 = "arith.mului_extended"(%5, %5) : (i32, i32) -> (i32, i32)
  %23 = "arith.ori"(%5, %5) : (i32, i32) -> i32
  %24 = "arith.remsi"(%5, %5) : (i32, i32) -> i32
  %25 = "arith.remui"(%5, %5) : (i32, i32) -> i32
  %26 = "arith.select"(%11, %5, %5) : (i1, i32, i32) -> i32
  %27 = "arith.shli"(%5, %5) : (i32, i32) -> i32
  %28 = "arith.shrsi"(%5, %5) : (i32, i32) -> i32
  %29 = "arith.shrui"(%5, %5) : (i32, i32) -> i32
  %30 = "arith.subi"(%5, %5) : (i32, i32) -> i32
  %31 = "arith.trunci"(%5) : (i32) -> i32
  %32 = "arith.xori"(%5, %5) : (i32, i32) -> i32
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT: ^4():
// CHECK-NEXT:   %5 = "arith.constant"() <{"value" = 13 : i32}> : () -> i32
// CHECK-NEXT:   %6 = "arith.addi"(%5, %5) : (i32, i32) -> i32
// CHECK-NEXT:   %7_0, %7_1 = "arith.addui_extended"(%5, %5) : (i32, i32) -> (i32, i32)
// CHECK-NEXT:   %8 = "arith.andi"(%5, %5) : (i32, i32) -> i32
// CHECK-NEXT:   %9 = "arith.ceildivsi"(%5, %5) : (i32, i32) -> i32
// CHECK-NEXT:   %10 = "arith.ceildivui"(%5, %5) : (i32, i32) -> i32
// CHECK-NEXT:   %11 = "arith.cmpi"(%5, %5) : (i32, i32) -> i1
// CHECK-NEXT:   %12 = "arith.divsi"(%5, %5) : (i32, i32) -> i32
// CHECK-NEXT:   %13 = "arith.divui"(%5, %5) : (i32, i32) -> i32
// CHECK-NEXT:   %14 = "arith.extui"(%5) : (i32) -> i32
// CHECK-NEXT:   %15 = "arith.floordivsi"(%5, %5) : (i32, i32) -> i32
// CHECK-NEXT:   %16 = "arith.maxsi"(%5, %5) : (i32, i32) -> i32
// CHECK-NEXT:   %17 = "arith.maxui"(%5, %5) : (i32, i32) -> i32
// CHECK-NEXT:   %18 = "arith.minsi"(%5, %5) : (i32, i32) -> i32
// CHECK-NEXT:   %19 = "arith.minui"(%5, %5) : (i32, i32) -> i32
// CHECK-NEXT:   %20 = "arith.muli"(%5, %5) : (i32, i32) -> i32
// CHECK-NEXT:   %21_0, %21_1 = "arith.mulsi_extended"(%5, %5) : (i32, i32) -> (i32, i32)
// CHECK-NEXT:   %22_0, %22_1 = "arith.mului_extended"(%5, %5) : (i32, i32) -> (i32, i32)
// CHECK-NEXT:   %23 = "arith.ori"(%5, %5) : (i32, i32) -> i32
// CHECK-NEXT:   %24 = "arith.remsi"(%5, %5) : (i32, i32) -> i32
// CHECK-NEXT:   %25 = "arith.remui"(%5, %5) : (i32, i32) -> i32
// CHECK-NEXT:   %26 = "arith.select"(%11, %5, %5) : (i1, i32, i32) -> i32
// CHECK-NEXT:   %27 = "arith.shli"(%5, %5) : (i32, i32) -> i32
// CHECK-NEXT:   %28 = "arith.shrsi"(%5, %5) : (i32, i32) -> i32
// CHECK-NEXT:   %29 = "arith.shrui"(%5, %5) : (i32, i32) -> i32
// CHECK-NEXT:   %30 = "arith.subi"(%5, %5) : (i32, i32) -> i32
// CHECK-NEXT:   %31 = "arith.trunci"(%5) : (i32) -> i32
// CHECK-NEXT:   %32 = "arith.xori"(%5, %5) : (i32, i32) -> i32
// CHECK-NEXT: }) : () -> ()
