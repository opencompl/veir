// RUN: veir-opt %s | filecheck %s

"builtin.module"() ({
  ^4():
    "func.func"() ({
      ^6(%arg6_0 : i32):
        "cf.br"(%arg6_0) [^6] : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^4():
// CHECK-NEXT:     "func.func"() ({
// CHECK-NEXT:       ^6(%arg6_0 : i32):
// CHECK-NEXT:         "cf.br"(%arg6_0) [^6] : (i32) -> ()
// CHECK-NEXT:   }) : () -> ()
// CHECK-NEXT: }) : () -> ()
