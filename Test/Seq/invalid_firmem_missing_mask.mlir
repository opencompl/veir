// RUN: not veir-opt %s 2>&1 | filecheck %s

// A masked memory's write port has to supply the mask.

// CHECK: seq.firmem.write_port: the memory has an i2 mask, which is missing

"builtin.module"() ({
  "hw.module"() <{module_type = !hw.modty<input clk : i1, input waddr : i2, input wdata : i8, input wen : i1, input raddr : i2, output rdata : i8>, parameters = [], per_port_attrs = [], sym_name = "ram"}> ({
  ^bb0(%clk: i1, %waddr: i2, %wdata: i8, %wen: i1, %raddr: i2):
    %clock = "seq.to_clock"(%clk) : (i1) -> !seq.clock
    %mem = "seq.firmem"() <{name = "mem", readLatency = 0 : i32, writeLatency = 1 : i32, ruw = 1 : i32, wuw = 1 : i32}> : () -> !seq.firmem<4 x 8, mask 2>
    %rd = "seq.firmem.read_port"(%mem, %raddr, %clock) : (!seq.firmem<4 x 8, mask 2>, i2, !seq.clock) -> i8
    "seq.firmem.write_port"(%mem, %waddr, %clock, %wen, %wdata) <{operandSegmentSizes = array<i32: 1, 1, 1, 1, 1, 0>}> : (!seq.firmem<4 x 8, mask 2>, i2, !seq.clock, i1, i8) -> ()
    "hw.output"(%rd) : (i8) -> ()
  }) : () -> ()
}) : () -> ()
