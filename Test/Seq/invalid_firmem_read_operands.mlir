// RUN: not veir-opt %s 2>&1 | filecheck %s

// A read port takes the memory, an address and a clock, plus an optional enable -- no more.

// CHECK: seq.firmem.read_port: Expected 3 or 4 operands

"builtin.module"() ({
  "hw.module"() <{module_type = !hw.modty<input clk : i1, input wen : i1, input raddr : i2, output rdata : i8>, parameters = [], per_port_attrs = [], sym_name = "ram"}> ({
  ^bb0(%clk: i1, %wen: i1, %raddr: i2):
    %clock = "seq.to_clock"(%clk) : (i1) -> !seq.clock
    %mem = "seq.firmem"() <{name = "mem", readLatency = 0 : i32, writeLatency = 1 : i32, ruw = 1 : i32, wuw = 1 : i32}> : () -> !seq.firmem<4 x 8>
    %rd = "seq.firmem.read_port"(%mem, %raddr, %clock, %wen, %wen) : (!seq.firmem<4 x 8>, i2, !seq.clock, i1, i1) -> i8
    "hw.output"(%rd) : (i8) -> ()
  }) : () -> ()
}) : () -> ()
