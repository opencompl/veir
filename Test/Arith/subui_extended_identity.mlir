// RUN: VEIR_ROUNDTRIP
// RUN: %if mlir-min-24 %{ MLIR_ROUNDTRIP %}

"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "main"}> ({
    ^0():
      %0 = "arith.constant"() <{ "value" = 13 : i32 }> : () -> i32
      %1, %2 = "arith.subui_extended"(%0, %0) : (i32, i32) -> (i32, i1)
      "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     "func.func"() <{"function_type" = () -> (), "sym_name" = "main"}> ({
// CHECK-NEXT:       ^{{.*}}():
// CHECK-NEXT:         %{{.*}} = "arith.constant"() <{"value" = 13 : i32}> : () -> i32
// CHECK-NEXT:         %{{.*}}:2 = "arith.subui_extended"(%{{.*}}, %{{.*}}) : (i32, i32) -> (i32, i1)
// CHECK-NEXT:         "func.return"() : () -> ()
