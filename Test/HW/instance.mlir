// RUN: VEIR_ROUNDTRIP

"builtin.module"() ({
  "hw.module"() <{comment = "", module_type = !hw.modty<input a : i8, input b : i8, output out : i8>, parameters = [], per_port_attrs = [], result_locs = [loc(unknown)], sym_name = "add2"}> ({
  ^bb0(%arg3: i8, %arg4: i8):
    %2 = "comb.add"(%arg3, %arg4) : (i8, i8) -> i8
    "hw.output"(%2) : (i8) -> ()
  }) {sym_visibility = "private"} : () -> ()
  "hw.module"() <{comment = "", module_type = !hw.modty<input a : i8, input b : i8, input c : i8, output out : i8>, parameters = [], per_port_attrs = [], result_locs = [loc(unknown)], sym_name = "add3"}> ({
  ^bb0(%arg0: i8, %arg1: i8, %arg2: i8):
    %0 = "hw.instance"(%arg0, %arg1) <{argNames = ["a", "b"], instanceName = "a0", moduleName = @add2, parameters = [], resultNames = ["out"]}> {sv.namehint = "s"} : (i8, i8) -> i8
    %1 = "hw.instance"(%arg2, %0) <{argNames = ["a", "b"], instanceName = "a1", moduleName = @add2, parameters = [], resultNames = ["out"]}> : (i8, i8) -> i8
    "hw.output"(%1) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     "hw.module"() <{"module_type" = !hw.modty<input a : i8, input b : i8, output out : i8>, "parameters" = [], "per_port_attrs" = [], "sym_name" = "add2"}> ({
// CHECK-NEXT:       ^{{.*}}(%{{.*}} : i8, %{{.*}} : i8):
// CHECK-NEXT:         %{{.*}} = "comb.add"(%{{.*}}, %{{.*}}) : (i8, i8) -> i8
// CHECK-NEXT:         "hw.output"(%{{.*}}) : (i8) -> ()
// CHECK-NEXT:     }) {"sym_visibility" = "private"} : () -> ()
// CHECK-NEXT:     "hw.module"() <{"module_type" = !hw.modty<input a : i8, input b : i8, input c : i8, output out : i8>, "parameters" = [], "per_port_attrs" = [], "sym_name" = "add3"}> ({
// CHECK-NEXT:       ^{{.*}}(%{{.*}} : i8, %{{.*}} : i8, %{{.*}} : i8):
// CHECK-NEXT:         %{{.*}} = "hw.instance"(%{{.*}}, %{{.*}}) <{"argNames" = ["a", "b"], "instanceName" = "a0", "moduleName" = @add2, "parameters" = [], "resultNames" = ["out"]}> {"sv.namehint" = "s"} : (i8, i8) -> i8
// CHECK-NEXT:         %{{.*}} = "hw.instance"(%{{.*}}, %{{.*}}) <{"argNames" = ["a", "b"], "instanceName" = "a1", "moduleName" = @add2, "parameters" = [], "resultNames" = ["out"]}> : (i8, i8) -> i8
// CHECK-NEXT:         "hw.output"(%{{.*}}) : (i8) -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT: }) : () -> ()
