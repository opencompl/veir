// RUN: veir-opt %s | filecheck %s

"builtin.module"() ({
  ^4():
    "func.func"() ({
      ^6(%arg6_0 : i32):
        "func.return"(%arg6_0) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^4():
// CHECK-NEXT:     "func.func"() ({
// CHECK-NEXT:       ^6(%arg6_0 : i32):
// CHECK-NEXT:         "func.return"(%arg6_0) : (i32) -> ()
// CHECK-NEXT:   }) : () -> ()
// CHECK-NEXT: }) : () -> ()
