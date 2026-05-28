// RUN: VEIR_ROUNDTRIP
"builtin.module"() ({
  // TODO(#675): the proper type should be without quotes, i.e.
  // `!cuda_tile.ptr<i1> -> ()`. Our parser cannot handle this right now, it's a
  // bug that should be fixed.
  "func.func"() <{function_type = "!cuda_tile.ptr<i1> -> ()", sym_name = "main"}> ({
    ^bb0(%arg0: !cuda_tile.ptr<i1>):
      %0 = "test.test"() : () -> !cuda_tile.ptr<i1>
      "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-NEXT: "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     "func.func"() <{"function_type" = "!cuda_tile.ptr<i1> -> ()", "sym_name" = "main"}> ({
// CHECK-NEXT:       ^{{.*}}(%{{.*}} : !cuda_tile.ptr<i1>):
// CHECK-NEXT:         %{{.*}} = "test.test"() : () -> !cuda_tile.ptr<i1>
// CHECK-NEXT:         "func.return"() : () -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT: }) : () -> ()
