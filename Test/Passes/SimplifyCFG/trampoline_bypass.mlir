// RUN: veir-opt %s -p=simplify-cfg | filecheck %s

"builtin.module"() ({
  "func.func"() <{"function_type" = (i32, i32) -> (), "sym_name" = "cf_br_chain"}> ({
    ^entry(%x : i32, %y : i32):
      "cf.br"(%y) [^mid] : (i32) -> ()
    ^mid(%m : i32):
      "cf.br"(%m) [^dst] : (i32) -> ()
    ^dst(%z : i32):
      "test.test"(%z) : (i32) -> ()
      "func.return"() : () -> ()
  }) : () -> ()

  "func.func"() <{"function_type" = (i1, i32, i32) -> (), "sym_name" = "cf_cond_edge"}> ({
    ^entry(%cond : i1, %x : i32, %y : i32):
      "cf.cond_br"(%cond, %x, %y) [^mid, ^other] <{"operandSegmentSizes" = array<i32: 1, 1, 1>}> : (i1, i32, i32) -> ()
    ^mid(%m : i32):
      "cf.br"(%m) [^dst] : (i32) -> ()
    ^other(%o : i32):
      "func.return"() : () -> ()
    ^dst(%z : i32):
      "func.return"() : () -> ()
  }) : () -> ()

  "func.func"() <{"function_type" = (i32, i32) -> (), "sym_name" = "llvm_br_chain"}> ({
    ^entry(%x : i32, %y : i32):
      "llvm.br"(%x) [^mid] : (i32) -> ()
    ^mid(%m : i32):
      "llvm.br"(%m) [^dst] : (i32) -> ()
    ^dst(%z : i32):
      "test.test"(%z) : (i32) -> ()
      "func.return"() : () -> ()
  }) : () -> ()

  "func.func"() <{"function_type" = (i1) -> (), "sym_name" = "not_empty_trampoline"}> ({
    ^entry(%cond : i1):
      "cf.cond_br"(%cond) [^pred1, ^pred2] <{"operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^pred1():
      "cf.br"() [^mid] : () -> ()
    ^pred2():
      "cf.br"() [^mid] : () -> ()
    ^mid():
      %c = "arith.constant"() <{"value" = 0 : i32}> : () -> i32
      "cf.br"(%c) [^dst] : (i32) -> ()
    ^dst(%z : i32):
      "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "func.func"() <{"function_type" = (i32, i32) -> (), "sym_name" = "cf_br_chain"}> ({
// CHECK-NEXT:   ^{{.*}}(%{{.*}} : i32, %[[Y:.*]] : i32):
// CHECK-NEXT:     "test.test"(%[[Y]]) : (i32) -> ()
// CHECK-NEXT:     "func.return"() : () -> ()
// CHECK-NOT:      "cf.br"
// CHECK:      }) : () -> ()

// CHECK:      "func.func"() <{"function_type" = (i1, i32, i32) -> (), "sym_name" = "cf_cond_edge"}> ({
// CHECK:          "cf.cond_br"(%{{.*}}, %{{.*}}, %{{.*}}) [^[[DST:[0-9]+]], ^[[OTHER:[0-9]+]]] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 1, 1>}> : (i1, i32, i32) -> ()
// CHECK:        ^[[DST]](%{{.*}} : i32):
// CHECK:        ^[[OTHER]](%{{.*}} : i32):
// CHECK:      }) : () -> ()

// CHECK:      "func.func"() <{"function_type" = (i32, i32) -> (), "sym_name" = "llvm_br_chain"}> ({
// CHECK-NEXT:   ^{{.*}}(%[[X:.*]] : i32, %{{.*}} : i32):
// CHECK-NEXT:     "test.test"(%[[X]]) : (i32) -> ()
// CHECK-NEXT:     "func.return"() : () -> ()
// CHECK-NOT:      "llvm.br"
// CHECK:      }) : () -> ()

// CHECK:      "func.func"() <{"function_type" = (i1) -> (), "sym_name" = "not_empty_trampoline"}> ({
// CHECK-NEXT:   ^{{.*}}(%{{.*}} : i1):
// CHECK-NEXT:     %{{.*}} = "arith.constant"() <{"value" = 0 : i32}> : () -> i32
// CHECK-NEXT:     "func.return"() : () -> ()
// CHECK-NOT:      "cf.br"
// CHECK:      }) : () -> ()
