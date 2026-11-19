// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_UNREGISTERED_ROUNDTRIP

// CHECK: ^{{.*}}(%[[CLK:[^ ]+]] : i1, %[[RST:[^ ]+]] : i1, %[[D:[^ ]+]] : i8):
// CHECK-NEXT: %[[CLOCK:[^ ]+]] = "seq.to_clock"(%[[CLK]]) : (i1) -> !seq.clock
// CHECK-NEXT: %[[INIT:[^ ]+]] = "seq.initial"() ({
// CHECK-NEXT: ^{{.*}}():
// CHECK-NEXT: %[[Z:[^ ]+]] = "hw.constant"() <{"value" = 0 : i8}> : () -> i8
// CHECK-NEXT: "seq.yield"(%[[Z]]) : (i8) -> ()
// CHECK-NEXT: }) : () -> !seq.immutable<i8>
// CHECK-NEXT: %[[A:[^ ]+]] = "seq.compreg"(%[[D]], %[[CLOCK]]) <{"inner_sym" = #hw<innerSym@a>, "name" = "a", "operandSegmentSizes" = array<i32: 1, 1, 0, 0, 0>}> : (i8, !seq.clock) -> i8
// CHECK-NEXT: %[[B:[^ ]+]] = "seq.compreg"(%[[A]], %[[CLOCK]], %[[INIT]]) <{"name" = "b", "operandSegmentSizes" = array<i32: 1, 1, 0, 0, 1>}> : (i8, !seq.clock, !seq.immutable<i8>) -> i8
// CHECK-NEXT: %[[C:[^ ]+]] = "seq.compreg"(%[[B]], %[[CLOCK]], %[[RST]], %[[Z2:[^ ]+]], %[[INIT]]) <{"operandSegmentSizes" = array<i32: 1, 1, 1, 1, 1>}> : (i8, !seq.clock, i1, i8, !seq.immutable<i8>) -> i8
// CHECK: "hw.output"(%[[C]]) : (i8) -> ()

"builtin.module"() ({
  "hw.module"() <{module_type = !hw.modty<input clk : i1, input rst : i1, input d : i8, output q : i8>, parameters = [], per_port_attrs = [], sym_name = "top"}> ({
  ^bb0(%clk: i1, %rst: i1, %d: i8):
    %clock = "seq.to_clock"(%clk) : (i1) -> !seq.clock
    %init = "seq.initial"() ({
      %z = "hw.constant"() <{value = 0 : i8}> : () -> i8
      "seq.yield"(%z) : (i8) -> ()
    }) : () -> !seq.immutable<i8>
    %a = "seq.compreg"(%d, %clock) <{inner_sym = #hw<innerSym@a>, name = "a", operandSegmentSizes = array<i32: 1, 1, 0, 0, 0>}> : (i8, !seq.clock) -> i8
    %b = "seq.compreg"(%a, %clock, %init) <{name = "b", operandSegmentSizes = array<i32: 1, 1, 0, 0, 1>}> : (i8, !seq.clock, !seq.immutable<i8>) -> i8
    %c = "seq.compreg"(%b, %clock, %rst, %zero, %init) <{operandSegmentSizes = array<i32: 1, 1, 1, 1, 1>}> : (i8, !seq.clock, i1, i8, !seq.immutable<i8>) -> i8
    %zero = "hw.constant"() <{value = 0 : i8}> : () -> i8
    "hw.output"(%c) : (i8) -> ()
  }) : () -> ()
}) : () -> ()
