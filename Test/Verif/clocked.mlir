// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_UNREGISTERED_ROUNDTRIP

// CHECK: "builtin.module"() ({
// CHECK-NEXT: ^{{.*}}():
// CHECK-NEXT: "hw.module"() <{{.*}}"sym_name" = "top"{{.*}}> ({
// CHECK-NEXT: ^{{.*}}(%[[CLK:[^ ]+]] : i1, %[[A:[^ ]+]] : i1, %[[EN:[^ ]+]] : i1):
// CHECK-NEXT: "verif.clocked_assert"(%[[A]], %[[CLK]], %[[EN]]) <{"edge" = 0 : i32, "label" = "x"}> : (i1, i1, i1) -> ()
// CHECK-NEXT: "verif.clocked_assert"(%[[A]], %[[CLK]]) <{"edge" = 1 : i32}> : (i1, i1) -> ()
// CHECK-NEXT: "verif.clocked_assume"(%[[A]], %[[CLK]]) <{"edge" = 2 : i32, "label" = "y"}> : (i1, i1) -> ()
// CHECK-NEXT: "verif.clocked_assume"(%[[A]], %[[CLK]], %[[EN]]) <{"edge" = 0 : i32}> : (i1, i1, i1) -> ()
// CHECK-NEXT: "hw.output"() : () -> ()
// CHECK-NEXT: }) : () -> ()
// CHECK-NEXT: }) : () -> ()

"builtin.module"() ({
  "hw.module"() <{module_type = !hw.modty<input clk : i1, input a : i1, input en : i1>, parameters = [], per_port_attrs = [], sym_name = "top"}> ({
  ^bb0(%clk: i1, %a: i1, %en: i1):
    "verif.clocked_assert"(%a, %clk, %en) <{edge = 0 : i32, label = "x"}> : (i1, i1, i1) -> ()
    "verif.clocked_assert"(%a, %clk) <{edge = 1 : i32}> : (i1, i1) -> ()
    "verif.clocked_assume"(%a, %clk) <{edge = 2 : i32, label = "y"}> : (i1, i1) -> ()
    "verif.clocked_assume"(%a, %clk, %en) <{edge = 0 : i32}> : (i1, i1, i1) -> ()
    "hw.output"() : () -> ()
  }) : () -> ()
}) : () -> ()
