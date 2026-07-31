// RUN: VEIR_ROUNDTRIP

"builtin.module"() ({
  // Define a type:
  %0 = "pdl.type"() : () -> !pdl.type
  // Define a type with a constant value:
  %1 = "pdl.type"() <{"constantType" = i32}> : () -> !pdl.type
  // The constant value can be any type, including another PDL handle type:
  %2 = "pdl.type"() <{"constantType" = !llvm.ptr}> : () -> !pdl.type
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     %{{.*}} = "pdl.type"() : () -> !pdl.type
// CHECK-NEXT:     %{{.*}} = "pdl.type"() <{"constantType" = i32}> : () -> !pdl.type
// CHECK-NEXT:     %{{.*}} = "pdl.type"() <{"constantType" = !llvm.ptr}> : () -> !pdl.type
// CHECK-NEXT: }) : () -> ()
