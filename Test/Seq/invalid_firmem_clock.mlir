// RUN: not veir-opt %s 2>&1 | filecheck %s

// A port's third operand is a clock, not an ordinary i1.

// CHECK: seq.firmem.read_port: expected the clock operand to be a '!seq.clock'

"builtin.module"() ({
  "hw.module"() <{module_type = !hw.modty<input clk : i1, input waddr : i2, input wdata : i8, input wen : i1, input raddr : i2, output rdata : i8>, parameters = [], per_port_attrs = [], sym_name = "ram"}> ({
  ^bb0(%clk: i1, %waddr: i2, %wdata: i8, %wen: i1, %raddr: i2):
    %clock = "seq.to_clock"(%clk) : (i1) -> !seq.clock
    %mem = "seq.firmem"() <{name = "mem", readLatency = 0 : i32, writeLatency = 1 : i32, ruw = 1 : i32, wuw = 1 : i32}> : () -> !seq.firmem<4 x 8>
    %rd = "seq.firmem.read_port"(%mem, %raddr, %wen) : (!seq.firmem<4 x 8>, i2, i1) -> i8
    "seq.firmem.write_port"(%mem, %waddr, %clock, %wen, %wdata) <{operandSegmentSizes = array<i32: 1, 1, 1, 1, 1, 0>}> : (!seq.firmem<4 x 8>, i2, !seq.clock, i1, i8) -> ()
    "hw.output"(%rd) : (i8) -> ()
  }) : () -> ()
}) : () -> ()
