// RUN: veir-opt %s | filecheck %s

"builtin.module"() ({
^bb0():
  %5 = "llvm.constant"() : () -> i32
  %6 = "llvm.constant"() : () -> i1
  %8 = "llvm.and"(%5, %5) : (i32, i32) -> i32
  %8 = "llvm.or"(%5, %5) : (i32, i32) -> i32
  %9 = "llvm.xor"(%5, %5) : (i32, i32) -> i32
  %10 = "llvm.add"(%5, %5) : (i32, i32) -> i32
  %11 = "llvm.sub"(%5, %5) : (i32, i32) -> i32
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
// CHECK-NEXT:     %5 = "llvm.constant"() : () -> i32
// CHECK-NEXT:     %6 = "llvm.constant"() : () -> i1
// CHECK-NEXT:     %7 = "llvm.and"(%5, %5) : (i32, i32) -> i32
// CHECK-NEXT:     %8 = "llvm.or"(%5, %5) : (i32, i32) -> i32
// CHECK-NEXT:     %9 = "llvm.xor"(%5, %5) : (i32, i32) -> i32
// CHECK-NEXT:     %10 = "llvm.add"(%5, %5) : (i32, i32) -> i32
// CHECK-NEXT:     %11 = "llvm.sub"(%5, %5) : (i32, i32) -> i32
// CHECK-NEXT:     %12 = "llvm.shl"(%5, %5) : (i32, i32) -> i32
// CHECK-NEXT:     %13 = "llvm.lshr"(%5, %5) : (i32, i32) -> i32
// CHECK-NEXT:     %14 = "llvm.ashr"(%5, %5) : (i32, i32) -> i32
// CHECK-NEXT:     %15 = "llvm.sdiv"(%5, %5) : (i32, i32) -> i32
// CHECK-NEXT:     %16 = "llvm.udiv"(%5, %5) : (i32, i32) -> i32
// CHECK-NEXT:     %17 = "llvm.urem"(%5, %5) : (i32, i32) -> i32
// CHECK-NEXT:     %18 = "llvm.srem"(%5, %5) : (i32, i32) -> i32
// CHECK-NEXT:     %19 = "llvm.icmp"(%5, %5) : (i32, i32) -> i1
// CHECK-NEXT:     %20 = "llvm.select"(%6, %5, %5) : (i1, i32, i32) -> i32
// CHECK-NEXT:     %21 = "llvm.trunc"(%5) : (i32) -> i1
// CHECK-NEXT:     %22 = "llvm.sext"(%6) : (i1) -> i32
// CHECK-NEXT:     %23 = "llvm.zext"(%6) : (i1) -> i32
// CHECK-NEXT:     "llvm.return"(%23) : (i32) -> ()
// CHECK-NEXT: }) : () -> ()
