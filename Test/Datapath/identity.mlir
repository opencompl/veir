// RUN: VEIR_ROUNDTRIP

"builtin.module"() ({
  "func.func"() <{function_type = (i3, i3, i3) -> (), sym_name = "main"}> ({
    ^bb0(%arg0: i3, %arg1: i3, %arg2: i3):
      %0, %1 = "datapath.compress"(%arg0, %arg1, %arg2) : (i3, i3, i3) -> (i3, i3)
      %2, %3, %4 = "datapath.partial_product"(%arg0, %arg1) : (i3, i3) -> (i3, i3, i3)
      %5, %6, %7 = "datapath.pos_partial_product"(%arg0, %arg1, %arg2) : (i3, i3, i3) -> (i3, i3, i3)
      "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     "func.func"() <{"function_type" = (i3, i3, i3) -> (), "sym_name" = "main"}> ({
// CHECK-NEXT:       ^{{.*}}(%{{.*}} : i3, %{{.*}} : i3, %{{.*}} : i3):
// CHECK-NEXT:         %{{.*}}:2 = "datapath.compress"(%{{.*}}, %{{.*}}, %{{.*}}) : (i3, i3, i3) -> (i3, i3)
// CHECK-NEXT:         %{{.*}}:3 = "datapath.partial_product"(%{{.*}}, %{{.*}}) : (i3, i3) -> (i3, i3, i3)
// CHECK-NEXT:         %{{.*}}:3 = "datapath.pos_partial_product"(%{{.*}}, %{{.*}}, %{{.*}}) : (i3, i3, i3) -> (i3, i3, i3)
// CHECK-NEXT:         "func.return"() : () -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT: }) : () -> ()
