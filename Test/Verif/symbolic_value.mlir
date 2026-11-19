// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_UNREGISTERED_ROUNDTRIP

// CHECK: "builtin.module"() ({
// CHECK-NEXT: ^{{.*}}():
// CHECK-NEXT: "hw.module"() <{{.*}}"sym_name" = "top"{{.*}}> ({
// CHECK-NEXT: ^{{.*}}():
// CHECK-NEXT: %[[A:[^ ]+]] = "verif.symbolic_value"() <{"name" = "a"}> : () -> i1
// CHECK-NEXT: %[[B:[^ ]+]] = "verif.symbolic_value"() : () -> i32
// CHECK-NEXT: "hw.output"(%[[A]], %[[B]]) : (i1, i32) -> ()
// CHECK-NEXT: }) : () -> ()
// CHECK-NEXT: }) : () -> ()

"builtin.module"() ({
  "hw.module"() <{module_type = !hw.modty<output x : i1, output y : i32>, parameters = [], per_port_attrs = [], sym_name = "top"}> ({
    %a = "verif.symbolic_value"() <{name = "a"}> : () -> i1
    %b = "verif.symbolic_value"() : () -> i32
    "hw.output"(%a, %b) : (i1, i32) -> ()
  }) : () -> ()
}) : () -> ()
