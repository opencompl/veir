// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_UNREGISTERED_ROUNDTRIP

// A module port can carry any type, not only an integer.

// CHECK: "hw.module"() <{"module_type" = !hw.modty<input clk : !seq.clock, input d : i8, output q : i8, output clk_out : !seq.clock>, "parameters" = [], "per_port_attrs" = [], "sym_name" = "top"}> ({
// CHECK-NEXT: ^{{.*}}(%[[CLK:[^ ]+]] : !seq.clock, %[[D:[^ ]+]] : i8):
// CHECK-NEXT: %[[Q:[^ ]+]] = "seq.compreg"(%[[D]], %[[CLK]]) <{"operandSegmentSizes" = array<i32: 1, 1, 0, 0, 0>}> : (i8, !seq.clock) -> i8
// CHECK-NEXT: "hw.output"(%[[Q]], %[[CLK]]) : (i8, !seq.clock) -> ()

"builtin.module"() ({
  "hw.module"() <{module_type = !hw.modty<input clk : !seq.clock, input d : i8, output q : i8, output clk_out : !seq.clock>, parameters = [], per_port_attrs = [], sym_name = "top"}> ({
  ^bb0(%clk: !seq.clock, %d: i8):
    %q = "seq.compreg"(%d, %clk) <{operandSegmentSizes = array<i32: 1, 1, 0, 0, 0>}> : (i8, !seq.clock) -> i8
    "hw.output"(%q, %clk) : (i8, !seq.clock) -> ()
  }) : () -> ()
}) : () -> ()
