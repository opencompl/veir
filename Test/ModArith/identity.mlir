// RUN: veir-opt %s | filecheck %s

"builtin.module"() ({
^bb0():
  %0 = "mod_arith.constant"() <{"value" = 13 : i32}> : () -> !mod_arith.int<17 : i32>
  %1 = "mod_arith.constant"() <{"value" = 7 : i32}> : () -> !mod_arith.int<17 : i32>
  %2 = "mod_arith.add"(%0, %1) : (!mod_arith.int<17 : i32>, !mod_arith.int<17 : i32>) -> !mod_arith.int<17 : i32>
  %3 = "mod_arith.sub"(%0, %1) : (!mod_arith.int<17 : i32>, !mod_arith.int<17 : i32>) -> !mod_arith.int<17 : i32>
  %4 = "mod_arith.mul"(%0, %1) : (!mod_arith.int<17 : i32>, !mod_arith.int<17 : i32>) -> !mod_arith.int<17 : i32>
}) : () -> ()


// CHECK:       "builtin.module"() ({
// CHECK-NEXT:   ^4():
// CHECK-NEXT:     %{{.*}} = "mod_arith.constant"() <{"value" = 13 : i32}> : () -> !mod_arith.int<17 : i32>
// CHECK-NEXT:     %{{.*}} = "mod_arith.constant"() <{"value" = 7 : i32}> : () -> !mod_arith.int<17 : i32>
// CHECK-NEXT:     %{{.*}} = "mod_arith.add"(%{{.*}}, %{{.*}}) : (!mod_arith.int<17 : i32>, !mod_arith.int<17 : i32>) -> !mod_arith.int<17 : i32>
// CHECK-NEXT:     %{{.*}} = "mod_arith.sub"(%{{.*}}, %{{.*}}) : (!mod_arith.int<17 : i32>, !mod_arith.int<17 : i32>) -> !mod_arith.int<17 : i32>
// CHECK-NEXT:     %{{.*}} = "mod_arith.mul"(%{{.*}}, %{{.*}}) : (!mod_arith.int<17 : i32>, !mod_arith.int<17 : i32>) -> !mod_arith.int<17 : i32>
// CHECK-NEXT: }) : () -> ()
