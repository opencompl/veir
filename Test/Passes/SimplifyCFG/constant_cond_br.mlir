// RUN: veir-opt %s -p=simplify-cfg | filecheck %s

"builtin.module"() ({
  "func.func"() <{"function_type" = (i32, i32) -> (), "sym_name" = "cf_false"}> ({
    ^entry(%x : i32, %y : i32):
      %c = "arith.constant"() <{"value" = 0 : i1}> : () -> i1
      "cf.cond_br"(%c, %x, %y) [^true, ^false] <{"operandSegmentSizes" = array<i32: 1, 1, 1>}> : (i1, i32, i32) -> ()
    ^true(%a : i32):
      "func.return"() : () -> ()
    ^false(%b : i32):
      "func.return"() : () -> ()
  }) : () -> ()

  "func.func"() <{"function_type" = (i32, i32) -> (), "sym_name" = "llvm_true"}> ({
    ^entry(%x : i32, %y : i32):
      %c = "llvm.mlir.constant"() <{"value" = 1 : i1}> : () -> i1
      "llvm.cond_br"(%c, %x, %y) [^true, ^false] <{"operandSegmentSizes" = array<i32: 1, 1, 1>}> : (i1, i32, i32) -> ()
    ^true(%a : i32):
      "func.return"() : () -> ()
    ^false(%b : i32):
      "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "func.func"() <{"function_type" = (i32, i32) -> (), "sym_name" = "cf_false"}> ({
// CHECK-NEXT:   ^{{.*}}(%{{.*}} : i32, %{{.*}} : i32):
// CHECK-NEXT:     %{{.*}} = "arith.constant"() <{"value" = 0 : i1}> : () -> i1
// CHECK-NEXT:     "func.return"() : () -> ()
// CHECK-NOT:      "cf.cond_br"
// CHECK-NOT:      "cf.br"
// CHECK:      }) : () -> ()

// CHECK:      "func.func"() <{"function_type" = (i32, i32) -> (), "sym_name" = "llvm_true"}> ({
// CHECK-NEXT:   ^{{.*}}(%{{.*}} : i32, %{{.*}} : i32):
// CHECK-NEXT:     %{{.*}} = "llvm.mlir.constant"() <{"value" = 1 : i1}> : () -> i1
// CHECK-NEXT:     "func.return"() : () -> ()
// CHECK-NOT:      "llvm.cond_br"
// CHECK-NOT:      "llvm.br"
// CHECK:      }) : () -> ()
