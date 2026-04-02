// RUN: veir-opt %s | filecheck %s

"builtin.module"() ({
^bb0():
  %0 = "llvm.constant"() <{"value" = 13 : i8}> : () -> i8
  %1 = "builtin.unrealized_conversion_cast"(%0) : (i8) -> !reg
  %2 = "builtin.unrealized_conversion_cast"(%1) : (!reg) -> i32
  // CHECK:          %{{.*}} = "llvm.constant"() <{"value" = 13 : i8}> : () -> i8
  // CHECK-NEXT:     %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i8) -> !reg
  // CHECK-NEXT:     %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!reg) -> i32
}) : () -> ()

