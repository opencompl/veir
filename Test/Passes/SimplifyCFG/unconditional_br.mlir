// RUN: veir-opt %s -p=simplify-cfg | filecheck %s

"builtin.module"() ({
  "func.func"() <{"function_type" = (i32, i32) -> (), "sym_name" = "cf_merge"}> ({
    ^entry(%x : i32, %y : i32):
      "cf.br"(%y) [^next] : (i32) -> ()
    ^next(%z : i32):
      "test.test"(%z) : (i32) -> ()
      "func.return"() : () -> ()
  }) : () -> ()

  "func.func"() <{"function_type" = (i32, i32) -> (), "sym_name" = "llvm_merge"}> ({
    ^entry(%x : i32, %y : i32):
      "llvm.br"(%x) [^next] : (i32) -> ()
    ^next(%z : i32):
      "test.test"(%z) : (i32) -> ()
      "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "func.func"() <{"function_type" = (i32, i32) -> (), "sym_name" = "cf_merge"}> ({
// CHECK-NEXT:   ^{{.*}}(%{{.*}} : i32, %[[Y:.*]] : i32):
// CHECK-NEXT:     "test.test"(%[[Y]]) : (i32) -> ()
// CHECK-NEXT:     "func.return"() : () -> ()
// CHECK-NOT:      "cf.br"
// CHECK:      }) : () -> ()

// CHECK:      "func.func"() <{"function_type" = (i32, i32) -> (), "sym_name" = "llvm_merge"}> ({
// CHECK-NEXT:   ^{{.*}}(%[[X:.*]] : i32, %{{.*}} : i32):
// CHECK-NEXT:     "test.test"(%[[X]]) : (i32) -> ()
// CHECK-NEXT:     "func.return"() : () -> ()
// CHECK-NOT:      "llvm.br"
// CHECK:      }) : () -> ()
