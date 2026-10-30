// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

// CHECK: "builtin.module"() ({
// CHECK-NEXT: ^{{.*}}():
// CHECK-NEXT: "func.func"() <{{.*}}"function_type" = (!smt.bv<8>) -> !smt.bool{{.*}}> ({
// CHECK-NEXT: ^{{.*}}(%{{.*}} : !smt.bv<8>):
// CHECK-NEXT: %{{.*}} = "smt.bv.neg"(%{{.*}}) : (!smt.bv<8>) -> !smt.bv<8>
// CHECK-NEXT: %{{.*}} = "smt.bv.add"(%{{.*}}, %{{.*}}) : (!smt.bv<8>, !smt.bv<8>) -> !smt.bv<8>
// CHECK-NEXT: %{{.*}} = "smt.eq"(%{{.*}}, %{{.*}}) : (!smt.bv<8>, !smt.bv<8>) -> !smt.bool
// CHECK-NEXT: "func.return"(%{{.*}}) : (!smt.bool) -> ()
// CHECK-NEXT: }) : () -> ()
// CHECK-NEXT: }) : () -> ()

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = (!smt.bv<8>) -> !smt.bool}> ({
  ^bb0(%arg0: !smt.bv<8>):
    %0 = "smt.bv.neg"(%arg0) : (!smt.bv<8>) -> !smt.bv<8>
    %1 = "smt.bv.add"(%0, %arg0) : (!smt.bv<8>, !smt.bv<8>) -> !smt.bv<8>
    %2 = "smt.eq"(%1, %arg0) : (!smt.bv<8>, !smt.bv<8>) -> !smt.bool
    "func.return"(%2) : (!smt.bool) -> ()
  }) : () -> ()
}) : () -> ()
