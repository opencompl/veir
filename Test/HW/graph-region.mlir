// RUN: VEIR_ROUNDTRIP

// An `hw.module` body is a graph region, so a register may close a feedback loop: the
// `comb.add` below reads the `seq.firreg` result that is only defined further down. The
// capture is taken at the use rather than the definition, because the use comes first.

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     "hw.module"() <{{{.*}}"sym_name" = "counter"{{.*}}> ({
// CHECK-NEXT:       ^{{.*}}(%[[CLK:[^ ]+]] : i1, %[[RST:[^ ]+]] : i1):
// CHECK-NEXT:         %[[CLOCK:[^ ]+]] = "seq.to_clock"(%[[CLK]]) : (i1) -> !seq.clock
// CHECK-NEXT:         %[[ZERO:[^ ]+]] = "hw.constant"() <{"value" = 0 : i8}> : () -> i8
// CHECK-NEXT:         %[[ONE:[^ ]+]] = "hw.constant"() <{"value" = 1 : i8}> : () -> i8
// CHECK-NEXT:         %[[INC:[^ ]+]] = "comb.add"(%[[Q:[^ ]+]], %[[ONE]]) : (i8, i8) -> i8
// CHECK-NEXT:         %[[NEXT:[^ ]+]] = "comb.mux"(%[[RST]], %[[ZERO]], %[[INC]]) : (i1, i8, i8) -> i8
// CHECK-NEXT:         %[[Q]] = "seq.firreg"(%[[NEXT]], %[[CLOCK]]) <{"name" = "q"}> : (i8, !seq.clock) -> i8
// CHECK-NEXT:         "hw.output"(%[[Q]]) : (i8) -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT: }) : () -> ()

"builtin.module"() ({
  "hw.module"() <{module_type = !hw.modty<input clk : i1, input rst : i1, output q : i8>, parameters = [], per_port_attrs = [], sym_name = "counter"}> ({
  ^bb0(%clk: i1, %rst: i1):
    %clock = "seq.to_clock"(%clk) : (i1) -> !seq.clock
    %zero = "hw.constant"() <{value = 0 : i8}> : () -> i8
    %one = "hw.constant"() <{value = 1 : i8}> : () -> i8
    %inc = "comb.add"(%q, %one) : (i8, i8) -> i8
    %next = "comb.mux"(%rst, %zero, %inc) : (i1, i8, i8) -> i8
    %q = "seq.firreg"(%next, %clock) <{name = "q"}> : (i8, !seq.clock) -> i8
    "hw.output"(%q) : (i8) -> ()
  }) : () -> ()
}) : () -> ()
