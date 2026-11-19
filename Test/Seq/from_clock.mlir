// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_UNREGISTERED_ROUNDTRIP

// CHECK: ^{{.*}}(%[[CLK:[^ ]+]] : i1):
// CHECK-NEXT: %[[CLOCK:[^ ]+]] = "seq.to_clock"(%[[CLK]]) : (i1) -> !seq.clock
// CHECK-NEXT: %[[BACK:[^ ]+]] = "seq.from_clock"(%[[CLOCK]]) : (!seq.clock) -> i1
// CHECK-NEXT: "hw.output"(%[[BACK]]) : (i1) -> ()

"builtin.module"() ({
  "hw.module"() <{module_type = !hw.modty<input clk : i1, output out : i1>, parameters = [], per_port_attrs = [], sym_name = "top"}> ({
  ^bb0(%clk: i1):
    %clock = "seq.to_clock"(%clk) : (i1) -> !seq.clock
    %back = "seq.from_clock"(%clock) : (!seq.clock) -> i1
    "hw.output"(%back) : (i1) -> ()
  }) : () -> ()
}) : () -> ()
