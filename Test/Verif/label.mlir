// RUN: VEIR_ROUNDTRIP

// CHECK: "builtin.module"() ({
// CHECK-NEXT: ^{{.*}}():
// CHECK-NEXT: "hw.module"() <{{.*}}"sym_name" = "top"{{.*}}> ({
// CHECK-NEXT: ^{{.*}}(%[[A:[^ ]+]] : i1):
// CHECK-NEXT: "verif.assume"(%[[A]]) <{"label" = "assumption"}> : (i1) -> ()
// CHECK-NEXT: "verif.assert"(%[[A]]) <{"label" = "assertion"}> : (i1) -> ()
// CHECK-NEXT:    "hw.output"() : () -> ()
// CHECK-NEXT:    }) : () -> ()
// CHECK-NEXT:  }) : () -> ()

"builtin.module"() ({
  "hw.module"() <{comment = "", module_type = !hw.modty<input a : i1>, parameters = [], per_port_attrs = [], result_locs = [], sym_name = "top"}> ({
  ^bb0(%arg0: i1):
    "verif.assume"(%arg0) <{label = "assumption"}> : (i1) -> ()
    "verif.assert"(%arg0) <{label = "assertion"}> : (i1) -> ()
    "hw.output"() : () -> ()
  }) : () -> ()
}) : () -> ()
