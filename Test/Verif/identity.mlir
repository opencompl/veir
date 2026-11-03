// RUN: VEIR_ROUNDTRIP

// CHECK: "builtin.module"() ({
// CHECK-NEXT:  ^{{.*}}():
// CHECK-NEXT: "hw.module"() <{{.*}}"sym_name" = "top"{{.*}}> ({
// CHECK-NEXT: ^{{.*}}(%[[A:[^ ]+]] : i1, %[[B:[^ ]+]] : i1):
// CHECK-NEXT: "verif.assume"(%[[A]]) : (i1) -> ()
// CHECK-NEXT: "verif.assume"(%[[A]], %[[B]]) : (i1, i1) -> ()
// CHECK-NEXT: "verif.assert"(%[[A]]) : (i1) -> ()
// CHECK-NEXT: "verif.assert"(%[[A]], %[[B]]) : (i1, i1) -> ()
// CHECK-NEXT:    "hw.output"() : () -> ()
// CHECK-NEXT:    }) : () -> ()
// CHECK-NEXT:  }) : () -> ()

"builtin.module"() ({
  "hw.module"() <{comment = "", module_type = !hw.modty<input a : i1, input b : i1>, parameters = [], per_port_attrs = [], result_locs = [], sym_name = "top"}> ({
  ^bb0(%arg0: i1, %arg1: i1):
    "verif.assume"(%arg0) : (i1) -> ()
    "verif.assume"(%arg0, %arg1) : (i1, i1) -> ()
    "verif.assert"(%arg0) : (i1) -> ()
    "verif.assert"(%arg0, %arg1) : (i1, i1) -> ()
    "hw.output"() : () -> ()
  }) : () -> ()
}) : () -> ()
