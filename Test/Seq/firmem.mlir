// RUN: VEIR_ROUNDTRIP

// `ram` is unmasked, and has a read port with its enable omitted, one with it supplied, and a
// write port. A read port carries no `operandSegmentSizes`: its lone optional operand is last.
// `maskedram` is masked, and uses the combined read-write port with every operand present.

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     "hw.module"() <{{{.*}}"sym_name" = "ram"{{.*}}> ({
// CHECK-NEXT:       ^{{.*}}(%[[CLK:[^ ]+]] : i1, %[[WADDR:[^ ]+]] : i2, %[[WDATA:[^ ]+]] : i8, %[[WEN:[^ ]+]] : i1, %[[RADDR:[^ ]+]] : i2):
// CHECK-NEXT:         %[[CLOCK:[^ ]+]] = "seq.to_clock"(%[[CLK]]) : (i1) -> !seq.clock
// CHECK-NEXT:         %[[MEM:[^ ]+]] = "seq.firmem"() <{{{.*}}"name" = "mem"{{.*}}"readLatency" = 0 : i32{{.*}}"ruw" = 1 : i32{{.*}}"writeLatency" = 1 : i32{{.*}}"wuw" = 1 : i32{{.*}}}> : () -> !seq.firmem<4 x 8>
// CHECK-NEXT:         %[[RD:[^ ]+]] = "seq.firmem.read_port"(%[[MEM]], %[[RADDR]], %[[CLOCK]]) : (!seq.firmem<4 x 8>, i2, !seq.clock) -> i8
// CHECK-NEXT:         %[[RDEN:[^ ]+]] = "seq.firmem.read_port"(%[[MEM]], %[[RADDR]], %[[CLOCK]], %[[WEN]]) : (!seq.firmem<4 x 8>, i2, !seq.clock, i1) -> i8
// CHECK-NEXT:         "seq.firmem.write_port"(%[[MEM]], %[[WADDR]], %[[CLOCK]], %[[WEN]], %[[WDATA]]) <{"operandSegmentSizes" = array<i32: 1, 1, 1, 1, 1, 0>}> : (!seq.firmem<4 x 8>, i2, !seq.clock, i1, i8) -> ()
// CHECK-NEXT:         "hw.output"(%[[RD]], %[[RDEN]]) : (i8, i8) -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT:     "hw.module"() <{{{.*}}"sym_name" = "maskedram"{{.*}}> ({
// CHECK-NEXT:       ^{{.*}}(%[[MCLK:[^ ]+]] : i1, %[[ADDR:[^ ]+]] : i3, %[[DATA:[^ ]+]] : i8, %[[EN:[^ ]+]] : i1, %[[MODE:[^ ]+]] : i1, %[[MASK:[^ ]+]] : i2):
// CHECK-NEXT:         %[[MCLOCK:[^ ]+]] = "seq.to_clock"(%[[MCLK]]) : (i1) -> !seq.clock
// CHECK-NEXT:         %[[MMEM:[^ ]+]] = "seq.firmem"() <{{{.*}}"ruw" = 2 : i32{{.*}}}> : () -> !seq.firmem<8 x 8, mask 2>
// CHECK-NEXT:         %[[RW:[^ ]+]] = "seq.firmem.read_write_port"(%[[MMEM]], %[[ADDR]], %[[MCLOCK]], %[[EN]], %[[DATA]], %[[MODE]], %[[MASK]]) <{"operandSegmentSizes" = array<i32: 1, 1, 1, 1, 1, 1, 1>}> : (!seq.firmem<8 x 8, mask 2>, i3, !seq.clock, i1, i8, i1, i2) -> i8
// CHECK-NEXT:         "hw.output"(%[[RW]]) : (i8) -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT: }) : () -> ()

"builtin.module"() ({
  "hw.module"() <{module_type = !hw.modty<input clk : i1, input waddr : i2, input wdata : i8, input wen : i1, input raddr : i2, output rdata : i8, output rdata_en : i8>, parameters = [], per_port_attrs = [], sym_name = "ram"}> ({
  ^bb0(%clk: i1, %waddr: i2, %wdata: i8, %wen: i1, %raddr: i2):
    %clock = "seq.to_clock"(%clk) : (i1) -> !seq.clock
    %mem = "seq.firmem"() <{name = "mem", readLatency = 0 : i32, writeLatency = 1 : i32, ruw = 1 : i32, wuw = 1 : i32}> : () -> !seq.firmem<4 x 8>
    %rd = "seq.firmem.read_port"(%mem, %raddr, %clock) : (!seq.firmem<4 x 8>, i2, !seq.clock) -> i8
    %rden = "seq.firmem.read_port"(%mem, %raddr, %clock, %wen) : (!seq.firmem<4 x 8>, i2, !seq.clock, i1) -> i8
    "seq.firmem.write_port"(%mem, %waddr, %clock, %wen, %wdata) <{operandSegmentSizes = array<i32: 1, 1, 1, 1, 1, 0>}> : (!seq.firmem<4 x 8>, i2, !seq.clock, i1, i8) -> ()
    "hw.output"(%rd, %rden) : (i8, i8) -> ()
  }) : () -> ()
  "hw.module"() <{module_type = !hw.modty<input clk : i1, input addr : i3, input data : i8, input en : i1, input mode : i1, input mask : i2, output rdata : i8>, parameters = [], per_port_attrs = [], sym_name = "maskedram"}> ({
  ^bb0(%clk: i1, %addr: i3, %data: i8, %en: i1, %mode: i1, %mask: i2):
    %clock = "seq.to_clock"(%clk) : (i1) -> !seq.clock
    %mem = "seq.firmem"() <{name = "mem", readLatency = 1 : i32, writeLatency = 1 : i32, ruw = 2 : i32, wuw = 1 : i32}> : () -> !seq.firmem<8 x 8, mask 2>
    %rw = "seq.firmem.read_write_port"(%mem, %addr, %clock, %en, %data, %mode, %mask) <{operandSegmentSizes = array<i32: 1, 1, 1, 1, 1, 1, 1>}> : (!seq.firmem<8 x 8, mask 2>, i3, !seq.clock, i1, i8, i1, i2) -> i8
    "hw.output"(%rw) : (i8) -> ()
  }) : () -> ()
}) : () -> ()
