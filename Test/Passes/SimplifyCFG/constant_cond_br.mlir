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
// CHECK-NEXT:     "cf.br"(%{{.*}}) [^[[CF_FALSE:[0-9]+]]] : (i32) -> ()
// CHECK-NEXT:   ^{{[0-9]+}}(%{{.*}} : i32):
// CHECK-NEXT:     "func.return"() : () -> ()
// CHECK-NEXT:   ^[[CF_FALSE]](%{{.*}} : i32):
// CHECK-NEXT:     "func.return"() : () -> ()
// CHECK-NEXT: }) : () -> ()

// CHECK:      "func.func"() <{"function_type" = (i32, i32) -> (), "sym_name" = "llvm_true"}> ({
// CHECK-NEXT:   ^{{.*}}(%{{.*}} : i32, %{{.*}} : i32):
// CHECK-NEXT:     %{{.*}} = "llvm.mlir.constant"() <{"value" = 1 : i1}> : () -> i1
// CHECK-NEXT:     "llvm.br"(%{{.*}}) [^[[LLVM_TRUE:[0-9]+]]] : (i32) -> ()
// CHECK-NEXT:   ^[[LLVM_TRUE]](%{{.*}} : i32):
// CHECK-NEXT:     "func.return"() : () -> ()
// CHECK-NEXT:   ^{{[0-9]+}}(%{{.*}} : i32):
// CHECK-NEXT:     "func.return"() : () -> ()
// CHECK-NEXT: }) : () -> ()
