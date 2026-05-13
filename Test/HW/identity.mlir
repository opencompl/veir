// RUN: veir-opt %s | filecheck %s

"builtin.module"() ({
^4():
  %1 = "hw.constant"() <{value = 13 : i10}> : () -> i10
  "hw.module"() <{module_type = !hw.modty<output a : i10, input b : i10>, parameters = [], result_locs = [loc("source.mlir":2:61), loc("source.mlir":2:73)], sym_name = "bar"}> ({
  ^bb0(%b: i10):
    "hw.output"(%b) : (i10) -> ()
  }) {sym_visibility = "public"} : () -> ()
  "hw.module"() <{module_type = !hw.modty<input a : i3, input b : i1, output c : i3, output d : i1>, parameters = [], result_locs = [loc("source.mlir":2:61), loc("source.mlir":2:73)], sym_name = "foo"}> ({
  ^bb0(%arg5: i3, %arg6: i1):
    "hw.output"(%arg5, %arg6) : (i3, i1) -> ()
  }) {sym_visibility = "private"} : () -> ()
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^4():
// CHECK-NEXT:     %{{.*}} = "hw.constant"() <{"value" = 13 : i10}> : () -> i10
// CHECK-NEXT:     "hw.module"() <{"module_type" = !hw.modty<output a : i10, input b : i10>, "parameters" = [], "per_port_attrs" = [], "sym_name" = "bar"}> ({
// CHECK-NEXT:       ^{{.*}}(%{{.*}}: i10):
// CHECK-NEXT:         "hw.output"(%{{.*}}) : (i10) -> ()
// CHECK-NEXT:     }) {"sym_visibility" = "public"} : () -> ()
// CHECK-NEXT:     "hw.module"() <{"module_type" = !hw.modty<input a : i3, input b : i1, output c : i3, output d : i1>, "parameters" = [], "per_port_attrs" = [], "sym_name" = "foo"}> ({
// CHECK-NEXT:       ^{{.*}}(%{{.*}} : i3, %{{.*}}: i1):
// CHECK-NEXT:         "hw.output"(%{{.*}}, %{{.*}}) : (i3, i1) -> ()
// CHECK-NEXT:     }) {"sym_visibility" = "private"} : () -> ()
// CHECK-NEXT: }) : () -> ()
