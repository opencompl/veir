// RUN: VEIR_UNREGISTERED_ROUNDTRIP
// RUN: MLIR_UNREGISTERED_ROUNDTRIP

"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "main"}> ({
    ^bb0():
      %0 = "test.test"() {map = affine_map<(d0, d1) -> (d1, 0)>} : () -> i32
      %1 = "test.test"() {map = affine_map<(d0, d1) -> ()>} : () -> i32
      %2 = "test.test"() {map = affine_map<() -> ()>} : () -> i32
      %3 = "test.test"() {map = affine_map<(d0) -> (-1)>} : () -> i32
      %4 = "test.test"() {map = affine_map<(i, j) -> (j, i)>} : () -> i32
      %5 = "test.test"() {maps = [affine_map<(d0, d1, d2) -> (d0, d2)>, affine_map<(d0, d1, d2) -> (d2, d1, d0)>]} : () -> i32
      "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-NEXT: "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     "func.func"() <{"function_type" = () -> (), "sym_name" = "main"}> ({
// CHECK-NEXT:       ^{{.*}}():
// CHECK-NEXT:         %{{.*}} = "test.test"() {"map" = affine_map<(d0, d1) -> (d1, 0)>} : () -> i32
// CHECK-NEXT:         %{{.*}} = "test.test"() {"map" = affine_map<(d0, d1) -> ()>} : () -> i32
// CHECK-NEXT:         %{{.*}} = "test.test"() {"map" = affine_map<() -> ()>} : () -> i32
// CHECK-NEXT:         %{{.*}} = "test.test"() {"map" = affine_map<(d0) -> (-1)>} : () -> i32
// CHECK-NEXT:         %{{.*}} = "test.test"() {"map" = affine_map<(d0, d1) -> (d1, d0)>} : () -> i32
// CHECK-NEXT:         %{{.*}} = "test.test"() {"maps" = [affine_map<(d0, d1, d2) -> (d0, d2)>, affine_map<(d0, d1, d2) -> (d2, d1, d0)>]} : () -> i32
// CHECK-NEXT:         "func.return"() : () -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT: }) : () -> ()
