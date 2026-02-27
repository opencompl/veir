// RUN: veir-opt %s | filecheck %s

"builtin.module"() ({
^bb0():
  %5 = "llvm.constant"() <{"value" = 13 : i32}> : () -> i32
  %6 = "llvm.constant"() <{"value" = 1 : i32}> : () -> i1
  %8 = "llvm.and"(%5, %5) : (i32, i32) -> i32
  %8 = "llvm.or"(%5, %5) : (i32, i32) -> i32
  %9 = "llvm.xor"(%5, %5) : (i32, i32) -> i32
  %add = "llvm.add"(%5, %5) : (i32, i32) -> i32
  %add_nsw = "llvm.add"(%5, %5) <{nsw}> : (i32, i32) -> i32
  %add_nuw = "llvm.add"(%5, %5) <{nuw}> : (i32, i32) -> i32
  %add_nsw_nuw = "llvm.add"(%5, %5) <{nsw, nuw}> : (i32, i32) -> i32
  %11 = "llvm.sub"(%5, %5) : (i32, i32) -> i32
  %mul = "llvm.mul"(%5, %5) : (i32, i32) -> i32
  %mul_nsw = "llvm.mul"(%5, %5) <{nsw}> : (i32, i32) -> i32
  %mul_nuw = "llvm.mul"(%5, %5) <{nuw}> : (i32, i32) -> i32
  %mul_nsw_nuw = "llvm.mul"(%5, %5) <{nsw, nuw}> : (i32, i32) -> i32
  %12 = "llvm.shl"(%5, %5) : (i32, i32) -> i32
  %13 = "llvm.lshr"(%5, %5) : (i32, i32) -> i32
  %14 = "llvm.ashr"(%5, %5) : (i32, i32) -> i32
  %15 = "llvm.sdiv"(%5, %5) : (i32, i32) -> i32
  %16 = "llvm.udiv"(%5, %5) : (i32, i32) -> i32
  %17 = "llvm.urem"(%5, %5) : (i32, i32) -> i32
  %18 = "llvm.srem"(%5, %5) : (i32, i32) -> i32
  %19 = "llvm.icmp"(%5, %5) : (i32, i32) -> i1
  %20 = "llvm.select"(%6, %5, %5) : (i1, i32, i32) -> i32
  %21 = "llvm.trunc"(%5) : (i32) -> i1
  %22 = "llvm.sext"(%6) : (i1) -> i32
  %23 = "llvm.zext"(%6) : (i1) -> i32
  "llvm.return"(%23) : (i32) -> ()
}) : () -> ()

// CHECK:       "builtin.module"() ({
// CHECK-NEXT:   ^4():
// CHECK-NEXT:     %{{.*}} = "llvm.constant"() <{"value" = 13 : i32}> : () -> i32
// CHECK-NEXT:     %{{.*}} = "llvm.constant"() <{"value" = 1 : i32}> : () -> i1
// CHECK-NEXT:     %{{.*}} = "llvm.and"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "llvm.or"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "llvm.xor"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "llvm.add"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "llvm.add"(%{{.*}}, %{{.*}}) <{nsw}> : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "llvm.add"(%{{.*}}, %{{.*}}) <{nuw}> : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "llvm.add"(%{{.*}}, %{{.*}}) <{nsw, nuw}> : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "llvm.sub"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "llvm.mul"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "llvm.mul"(%{{.*}}, %{{.*}}) <{nsw}> : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "llvm.mul"(%{{.*}}, %{{.*}}) <{nuw}> : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "llvm.mul"(%{{.*}}, %{{.*}}) <{nsw, nuw}> : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "llvm.shl"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "llvm.lshr"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "llvm.ashr"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "llvm.sdiv"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "llvm.udiv"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "llvm.urem"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "llvm.srem"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "llvm.icmp"(%{{.*}}, %{{.*}}) : (i32, i32) -> i1
// CHECK-NEXT:     %{{.*}} = "llvm.select"(%{{.*}}, %{{.*}}, %{{.*}}) : (i1, i32, i32) -> i32
// CHECK-NEXT:     %{{.*}} = "llvm.trunc"(%{{.*}}) : (i32) -> i1
// CHECK-NEXT:     %{{.*}} = "llvm.sext"(%{{.*}}) : (i1) -> i32
// CHECK-NEXT:     %{{.*}} = "llvm.zext"(%{{.*}}) : (i1) -> i32
// CHECK-NEXT:     "llvm.return"(%{{.*}}) : (i32) -> ()
// CHECK-NEXT: }) : () -> ()
