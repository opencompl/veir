// RUN: VEIR_ROUNDTRIP

// CHECK: "builtin.module"() ({
// CHECK-NEXT:  ^{{.*}}():
// CHECK-NEXT: "hw.module"() <{{{.*}}"sym_name" = "top"{{.*}}> ({
// CHECK-NEXT: ^{{.*}}(%[[CLK:[^ ]+]] : i1, %[[RST:[^ ]+]] : i1, %[[D:[^ ]+]] : i1):
// CHECK-NEXT: %[[CLOCK:[^ ]+]] = "seq.to_clock"(%[[CLK]]) : (i1) -> !seq.clock
// CHECK-NEXT: %[[Q:[^ ]+]] = "seq.firreg"(%[[D]], %[[CLOCK]]) <{{{.*}}"name" = "q"{{.*}}}> : (i1, !seq.clock) -> i1
// CHECK-NEXT:    "hw.output"(%[[Q]]) : (i1) -> ()
// CHECK-NEXT:    }) : () -> ()
// CHECK-NEXT:  }) : () -> ()

"builtin.module"() ({
  "hw.module"() <{comment = "", module_type = !hw.modty<input clk : i1, input rst : i1, input d : i1, output q : i1>, parameters = [], per_port_attrs = [], result_locs = [loc(unknown)], sym_name = "top"}> ({
  ^bb0(%arg0: i1, %arg1: i1, %arg2: i1):
    %0 = "seq.to_clock"(%arg0) : (i1) -> !seq.clock
    %1 = "seq.firreg"(%arg2, %0) <{name = "q"}> : (i1, !seq.clock) -> i1
    "hw.output"(%1) : (i1) -> ()
  }) : () -> ()
}) : () -> ()
