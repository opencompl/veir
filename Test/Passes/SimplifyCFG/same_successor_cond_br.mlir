// RUN: veir-opt %s -p=simplify-cfg | filecheck %s

"builtin.module"() ({
  "func.func"() <{"function_type" = (i1, i32) -> (), "sym_name" = "cf_same_successor"}> ({
    ^entry(%cond : i1, %x : i32):
      "cf.cond_br"(%cond, %x, %x) [^next, ^next] <{"operandSegmentSizes" = array<i32: 1, 1, 1>}> : (i1, i32, i32) -> ()
    ^next(%z : i32):
      "test.test"(%z) : (i32) -> ()
      "func.return"() : () -> ()
  }) : () -> ()

  "func.func"() <{"function_type" = (i1, i32) -> (), "sym_name" = "llvm_same_successor"}> ({
    ^entry(%cond : i1, %x : i32):
      "llvm.cond_br"(%cond, %x, %x) [^next, ^next] <{"operandSegmentSizes" = array<i32: 1, 1, 1>}> : (i1, i32, i32) -> ()
    ^next(%z : i32):
      "test.test"(%z) : (i32) -> ()
      "func.return"() : () -> ()
  }) : () -> ()

  "func.func"() <{"function_type" = (i1, i32, i32) -> (), "sym_name" = "different_args"}> ({
    ^entry(%cond : i1, %x : i32, %y : i32):
      "cf.cond_br"(%cond, %x, %y) [^next, ^next] <{"operandSegmentSizes" = array<i32: 1, 1, 1>}> : (i1, i32, i32) -> ()
    ^next(%z : i32):
      "test.test"(%z) : (i32) -> ()
      "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "func.func"() <{"function_type" = (i1, i32) -> (), "sym_name" = "cf_same_successor"}> ({
// CHECK-NEXT:   ^{{.*}}(%{{.*}} : i1, %[[X:.*]] : i32):
// CHECK-NEXT:     "test.test"(%[[X]]) : (i32) -> ()
// CHECK-NEXT:     "func.return"() : () -> ()
// CHECK-NOT:      "cf.cond_br"
// CHECK-NOT:      "cf.br"
// CHECK:      }) : () -> ()

// CHECK:      "func.func"() <{"function_type" = (i1, i32) -> (), "sym_name" = "llvm_same_successor"}> ({
// CHECK-NEXT:   ^{{.*}}(%{{.*}} : i1, %[[Y:.*]] : i32):
// CHECK-NEXT:     "test.test"(%[[Y]]) : (i32) -> ()
// CHECK-NEXT:     "func.return"() : () -> ()
// CHECK-NOT:      "llvm.cond_br"
// CHECK-NOT:      "llvm.br"
// CHECK:      }) : () -> ()

// CHECK:      "func.func"() <{"function_type" = (i1, i32, i32) -> (), "sym_name" = "different_args"}> ({
// CHECK:          "cf.cond_br"(%{{.*}}, %{{.*}}, %{{.*}}) [^[[DST:[0-9]+]], ^[[DST]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 1, 1>}> : (i1, i32, i32) -> ()
// CHECK:      }) : () -> ()
