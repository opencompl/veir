// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

"builtin.module"() ({
  "func.func"() <{sym_name = "f", function_type = (f80, f128) -> (f80, f128)}> ({
  ^bb0(%x: f80, %y: f128):
    "func.return"(%x, %y) : (f80, f128) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "func.func"() <{"function_type" = (f80, f128) -> (f80, f128), "sym_name" = "f"}> ({
// CHECK-NEXT: ^{{.*}}(%{{.*}} : f80, %{{.*}} : f128):
