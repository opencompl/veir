// RUN: veir-opt %s | filecheck %s

"builtin.module"() ({
^4():
  %5 = "arith.constant"() <{ "value" = 13 : i32 }> : () -> i32
  %addi = "arith.addi"(%5, %5) : (i32, i32) -> i32
  %addi_nsw = "arith.addi"(%5, %5) <{nws}> : (i32, i32) -> i32
  %addi_nuw = "arith.addi"(%5, %5) <{nuw}> : (i32, i32) -> i32
  %addi_nsw_nuw = "arith.addi"(%5, %5) <{nsw, nuw}> : (i32, i32) -> i32
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
  %muli = "arith.muli"(%5, %5) : (i32, i32) -> i32
  %muli_nsw = "arith.muli"(%5, %5) <{nws}> : (i32, i32) -> i32
  %muli_nuw = "arith.muli"(%5, %5) <{nuw}> : (i32, i32) -> i32
  %muli_nsw_nuw = "arith.muli"(%5, %5) <{nsw, nuw}> : (i32, i32) -> i32
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
// CHECK-NEXT:   ^4():
// CHECK-NEXT:     %{{.*}} = "arith.constant"() <{"value" = 13 : i32}> : () -> i32
// CHECK-NEXT:     %{{.*}} = "arith.addi"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "arith.addi"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "arith.addi"(%{{.*}}, %{{.*}}) <{nuw}> : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "arith.addi"(%{{.*}}, %{{.*}}) <{nsw, nuw}> : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}}, %{{.*}} = "arith.addui_extended"(%{{.*}}, %{{.*}}) : (i32, i32) -> (i32, i32)
// CHECK-NEXT:     %{{.*}} = "arith.andi"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "arith.ceildivsi"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "arith.ceildivui"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "arith.cmpi"(%{{.*}}, %{{.*}}) : (i32, i32) -> i1
// CHECK-NEXT:     %{{.*}} = "arith.divsi"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "arith.divui"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "arith.extui"(%{{.*}}) : (i32) -> i32
// CHECK-NEXT:     %{{.*}} = "arith.floordivsi"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "arith.maxsi"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "arith.maxui"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "arith.minsi"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "arith.minui"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "arith.muli"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "arith.muli"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "arith.muli"(%{{.*}}, %{{.*}}) <{nuw}> : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "arith.muli"(%{{.*}}, %{{.*}}) <{nsw, nuw}> : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}}, %{{.*}} = "arith.mulsi_extended"(%{{.*}}, %{{.*}}) : (i32, i32) -> (i32, i32)
// CHECK-NEXT:     %{{.*}}, %{{.*}} = "arith.mului_extended"(%{{.*}}, %{{.*}}) : (i32, i32) -> (i32, i32)
// CHECK-NEXT:     %{{.*}} = "arith.ori"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "arith.remsi"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "arith.remui"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "arith.select"(%{{.*}}, %{{.*}}, %{{.*}}) : (i1, i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "arith.shli"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "arith.shrsi"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "arith.shrui"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "arith.subi"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "arith.trunci"(%{{.*}}) : (i32) -> i32
// CHECK-NEXT:     %{{.*}} = "arith.xori"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT: }) : () -> ()
