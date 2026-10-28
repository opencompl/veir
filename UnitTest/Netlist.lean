import Veir.Interpreter.Netlist
import Veir.Input

/-! Tests for the `hw.module` netlist simulator.

The modules are parsed from text here, which is the convenient way to write a test and not how a
caller is expected to build one -- `Veir.Netlist` takes a `WfIRContext` however it was made.

What is being checked is the part a CFG interpreter has no analogue for: that a register holds its
value between edges, that ticking one clock leaves another domain alone, that a memory read in the
cycle of a write sees the *old* word, and that two writes to one address land in port order.
-/

open Veir

private def parseModule (text : String) : Option (WfIRContext OpCode × OperationPtr) := do
  let .ok (ctx, top, _) := Veir.Input.parseSourceString text.toUTF8 "test" | none
  -- The `hw.module` is the first operation inside the top-level `builtin.module`.
  if top.getNumRegions! ctx.raw == 0 then none
  let region := top.getRegion! ctx.raw 0
  let some block := region.getFirstBlock! ctx.raw | none
  let some hwModule := block.getFirstOp! ctx.raw | none
  return (ctx, hwModule)

/-- Build the module, then tick `(clock index, input values)` in order, returning the output port
values after every tick. -/
private def run (text : String) (ticks : List (Nat × Array RuntimeValue)) :
    Option (List (Array Nat)) := do
  let (ctx, hwModule) ← parseModule text
  let info ← Netlist.Info.of ctx hwModule
  let mut st ← Netlist.State.init ctx info
  let mut out : List (Array Nat) := []
  for (clock, args) in ticks do
    st ← Netlist.stepClock ctx info clock args st
    let (vals, _) ← Netlist.settle ctx info args st
    let outs ← Netlist.outputs ctx info vals
    out := out ++ [← outs.mapM fun v =>
      match v with
      | .int _ (.val b) => some b.toNat
      | _ => none]
  return out

private def i (w v : Nat) : RuntimeValue := .int w (.val (BitVec.ofNat w v))

/-! ### A register holds between edges, and feeds itself

The counter is also the smallest case of the graph region this driver depends on: `comb.add`
reads `%1` two lines before `seq.firreg` defines it.
-/

private def counter : String :=
"\"builtin.module\"() ({
^bb0():
  \"hw.module\"() <{module_type = !hw.modty<input clk : i1, input rst : i1, output q : i8>, parameters = [], per_port_attrs = [], sym_name = \"counter\"}> ({
  ^bb1(%arg0: i1, %arg1: i1):
    %0 = \"seq.to_clock\"(%arg0) : (i1) -> !seq.clock
    %2 = \"hw.constant\"() <{\"value\" = 0 : i8}> : () -> i8
    %3 = \"hw.constant\"() <{\"value\" = 1 : i8}> : () -> i8
    %4 = \"comb.add\"(%1, %3) : (i8, i8) -> i8
    %5 = \"comb.mux\"(%arg1, %2, %4) : (i1, i8, i8) -> i8
    %1 = \"seq.firreg\"(%5, %0) <{\"name\" = \"q\"}> : (i8, !seq.clock) -> i8
    \"hw.output\"(%1) : (i8) -> ()
  }) : () -> ()
}) : () -> ()"

private def testCounter : String := Id.run do
  let lo : Array RuntimeValue := #[i 1 0, i 1 0]
  let some trace := run counter (List.replicate 4 (0, lo)) | return "did not simulate"
  if trace != [#[1], #[2], #[3], #[4]] then return s!"counted {trace}"
  -- With reset held, the mux feeds zero in and the register never advances.
  let rst : Array RuntimeValue := #[i 1 0, i 1 1]
  let some held := run counter [(0, lo), (0, lo), (0, rst), (0, lo)] | return "did not simulate"
  if held != [#[1], #[2], #[0], #[1]] then return s!"reset {held}"
  return "ok"

/-- info: "ok" -/
#guard_msgs in
#eval! testCounter

/-! ### Two clock domains advance independently

The property that makes this a *netlist* driver rather than an op evaluator: `stepClock` fires the
registers on one clock and leaves the rest where they were. A simulator that ignored the clock
operand would pass every test above and fail this one.
-/

private def twoClock : String :=
"\"builtin.module\"() ({
^bb0():
  \"hw.module\"() <{module_type = !hw.modty<input clkA : i1, input clkB : i1, output p : i8, output q : i8>, parameters = [], per_port_attrs = [], sym_name = \"twoClock\"}> ({
  ^bb1(%arg0: i1, %arg1: i1):
    %0 = \"seq.to_clock\"(%arg0) : (i1) -> !seq.clock
    %1 = \"seq.to_clock\"(%arg1) : (i1) -> !seq.clock
    %2 = \"hw.constant\"() <{\"value\" = 1 : i8}> : () -> i8
    %4 = \"comb.add\"(%3, %2) : (i8, i8) -> i8
    %3 = \"seq.firreg\"(%4, %0) <{\"name\" = \"p\"}> : (i8, !seq.clock) -> i8
    %6 = \"comb.add\"(%5, %2) : (i8, i8) -> i8
    %5 = \"seq.firreg\"(%6, %1) <{\"name\" = \"q\"}> : (i8, !seq.clock) -> i8
    \"hw.output\"(%3, %5) : (i8, i8) -> ()
  }) : () -> ()
}) : () -> ()"

private def testTwoClock : String := Id.run do
  let args : Array RuntimeValue := #[i 1 0, i 1 0]
  -- Three ticks of clkA, then one of clkB.
  let some trace := run twoClock [(0, args), (0, args), (0, args), (1, args)] | return "no sim"
  if trace != [#[1, 0], #[2, 0], #[3, 0], #[3, 1]] then return s!"domains {trace}"
  return "ok"

/-- info: "ok" -/
#guard_msgs in
#eval! testTwoClock

/-! ### Memory: read-under-write is `old`, write-under-write is port order

`ruw = old` is what makes a non-blocking store in a source language come out right, and it is not
observable from anything but a read in the same cycle as a write to the same address.
-/

private def mem1 : String :=
"\"builtin.module\"() ({
^bb0():
  \"hw.module\"() <{module_type = !hw.modty<input clk : i1, input we : i1, input addr : i2, input din : i8, output dout : i8>, parameters = [], per_port_attrs = [], sym_name = \"mem1\"}> ({
  ^bb1(%arg0: i1, %arg1: i1, %arg2: i2, %arg3: i8):
    %0 = \"seq.to_clock\"(%arg0) : (i1) -> !seq.clock
    %1 = \"seq.firmem\"() <{\"name\" = \"mem\", \"readLatency\" = 0 : i32, \"writeLatency\" = 1 : i32, \"ruw\" = 1 : i32, \"wuw\" = 1 : i32}> : () -> !seq.firmem<4 x 8>
    %2 = \"seq.firmem.read_port\"(%1, %arg2, %0) : (!seq.firmem<4 x 8>, i2, !seq.clock) -> i8
    \"seq.firmem.write_port\"(%1, %arg2, %0, %arg1, %arg3) <{\"operandSegmentSizes\" = array<i32: 1, 1, 1, 1, 1, 0>}> : (!seq.firmem<4 x 8>, i2, !seq.clock, i1, i8) -> ()
    \"hw.output\"(%2) : (i8) -> ()
  }) : () -> ()
}) : () -> ()"

/-- Settle without taking an edge, to see what a port offers *during* a cycle. -/
private def duringWrite : Option Nat := do
  let (ctx, hwModule) ← parseModule mem1
  let info ← Netlist.Info.of ctx hwModule
  let st ← Netlist.State.init ctx info
  let args : Array RuntimeValue := #[i 1 0, i 1 1, i 2 1, i 8 77]
  let (vals, writes) ← Netlist.settle ctx info args st
  -- The write is enabled, so it was collected rather than applied.
  if writes.size != 1 then none
  let outs ← Netlist.outputs ctx info vals
  match (outs[0]? : Option RuntimeValue) with
  | some (.int _ (.val b)) => some b.toNat
  | _ => none

private def testMemory : String := Id.run do
  -- Write 77 to address 1, then read address 1, then address 0.
  let wr : Array RuntimeValue := #[i 1 0, i 1 1, i 2 1, i 8 77]
  let rd1 : Array RuntimeValue := #[i 1 0, i 1 0, i 2 1, i 8 0]
  let rd0 : Array RuntimeValue := #[i 1 0, i 1 0, i 2 0, i 8 0]
  let some trace := run mem1 [(0, wr), (0, rd1), (0, rd0)] | return "no sim"
  if trace != [#[77], #[77], #[0]] then return s!"memory {trace}"
  -- `ruw = old`: in the cycle of the write, the read port still offers the old word.
  if duringWrite != some 0 then return s!"read-under-write gave {duringWrite}"
  -- A disabled write does nothing, so an unconditionally enabled write port would be caught.
  let noWr : Array RuntimeValue := #[i 1 0, i 1 0, i 2 1, i 8 77]
  let some quiet := run mem1 [(0, noWr), (0, rd1)] | return "no sim"
  if quiet != [#[0], #[0]] then return s!"disabled write {quiet}"
  return "ok"

/-- info: "ok" -/
#guard_msgs in
#eval! testMemory

/-! ### A memory belongs to one clock domain too

`mem1` has a single clock, so nothing in it can tell whether a pending write is being filtered by
the clock being ticked or simply applied to whatever edge comes next. This is the memory
counterpart of `testTwoClock`: the write port is tied to `clkA`, so ticking `clkB` must leave the
memory alone.
-/

private def memTwoClock : String :=
"\"builtin.module\"() ({
^bb0():
  \"hw.module\"() <{module_type = !hw.modty<input clkA : i1, input clkB : i1, input we : i1, input addr : i2, input din : i8, output dout : i8>, parameters = [], per_port_attrs = [], sym_name = \"memTwoClock\"}> ({
  ^bb1(%arg0: i1, %arg1: i1, %arg2: i1, %arg3: i2, %arg4: i8):
    %0 = \"seq.to_clock\"(%arg0) : (i1) -> !seq.clock
    %1 = \"seq.to_clock\"(%arg1) : (i1) -> !seq.clock
    %2 = \"seq.firmem\"() <{\"name\" = \"mem\", \"readLatency\" = 0 : i32, \"writeLatency\" = 1 : i32, \"ruw\" = 1 : i32, \"wuw\" = 1 : i32}> : () -> !seq.firmem<4 x 8>
    %3 = \"seq.firmem.read_port\"(%2, %arg3, %0) : (!seq.firmem<4 x 8>, i2, !seq.clock) -> i8
    \"seq.firmem.write_port\"(%2, %arg3, %0, %arg2, %arg4) <{\"operandSegmentSizes\" = array<i32: 1, 1, 1, 1, 1, 0>}> : (!seq.firmem<4 x 8>, i2, !seq.clock, i1, i8) -> ()
    %4 = \"seq.firreg\"(%arg4, %1) <{\"name\" = \"unused\"}> : (i8, !seq.clock) -> i8
    \"hw.output\"(%3) : (i8) -> ()
  }) : () -> ()
}) : () -> ()"

private def testMemoryClockDomain : String := Id.run do
  -- clkA, clkB, we, addr, din
  let wr : Array RuntimeValue := #[i 1 0, i 1 0, i 1 1, i 2 1, i 8 55]
  let rd : Array RuntimeValue := #[i 1 0, i 1 0, i 1 0, i 2 1, i 8 0]
  -- Ticking the *other* domain must not apply the write.
  match run memTwoClock [(1, wr), (0, rd)] with
  | none => return "the module did not simulate"
  | some trace => if trace != [#[0], #[0]] then return s!"clkB applied the write: {trace}"
  -- Control: ticking the write port's own domain does apply it.
  match run memTwoClock [(0, wr), (0, rd)] with
  | none => return "the module did not simulate on clkA"
  | some trace => if trace != [#[55], #[55]] then return s!"clkA did not apply the write: {trace}"
  return "ok"

/-- info: "ok" -/
#guard_msgs in
#eval! testMemoryClockDomain

/-! ### Unmodelled memory modes are refused

`ruw = new` is a real CIRCT behaviour and this driver does not implement it. Returning `none`
rather than simulating `old` anyway is what stops a caller proving something about a module whose
meaning it got wrong -- a lesson paid for once already in the package that drove this work.
-/

private def memRuwNew : String :=
  mem1.replace "\"ruw\" = 1 : i32" "\"ruw\" = 0 : i32" |>.replace "\"mem1\"" "\"memRuwNew\""

private def testRefusesUnmodelled : String := Id.run do
  let args : Array RuntimeValue := #[i 1 0, i 1 0, i 2 0, i 8 0]
  if (run memRuwNew [(0, args)]).isSome then return "ruw = new was simulated anyway"
  -- And the control: the same module with `ruw = old` does simulate, so the refusal above is
  -- about the attribute and not about the module failing to parse.
  if (run mem1 [(0, args)]).isNone then return "ruw = old failed to simulate"
  return "ok"

/-- info: "ok" -/
#guard_msgs in
#eval! testRefusesUnmodelled

/-! ### The other things the driver refuses

Each of these is a real CIRCT behaviour the driver does not model. The header claims it refuses
them; these are what make that claim true rather than aspirational. `isAsync` and `preset` were
in fact *not* checked when that paragraph was first written, and nothing noticed.

Every case is paired with the unaltered module, so a refusal is known to be about the thing that
changed and not about the test module failing to parse.
-/

private def counterAsync : String :=
  counter.replace "<{\"name\" = \"q\"}>" "<{\"name\" = \"q\", \"isAsync\"}>"
    |>.replace "\"counter\"" "\"counterAsync\""

private def counterPreset : String :=
  counter.replace "<{\"name\" = \"q\"}>" "<{\"name\" = \"q\", \"preset\" = 3 : i8}>"
    |>.replace "\"counter\"" "\"counterPreset\""

private def memBadLatency : String :=
  mem1.replace "\"readLatency\" = 0 : i32" "\"readLatency\" = 1 : i32"
    |>.replace "\"mem1\"" "\"memBadLatency\""

private def memWuwNew : String :=
  mem1.replace "\"wuw\" = 1 : i32" "\"wuw\" = 0 : i32" |>.replace "\"mem1\"" "\"memWuwNew\""

/-- A register clocked by something that is not a `seq.to_clock` of a block argument. A derived or
gated clock is perfectly good hardware and this driver cannot say when it ticks. -/
private def derivedClock : String :=
"\"builtin.module\"() ({
^bb0():
  \"hw.module\"() <{module_type = !hw.modty<input clk : i1, input g : i1, output q : i8>, parameters = [], per_port_attrs = [], sym_name = \"derivedClock\"}> ({
  ^bb1(%arg0: i1, %arg1: i1):
    %0 = \"comb.and\"(%arg0, %arg1) : (i1, i1) -> i1
    %1 = \"seq.to_clock\"(%0) : (i1) -> !seq.clock
    %3 = \"hw.constant\"() <{\"value\" = 1 : i8}> : () -> i8
    %4 = \"comb.add\"(%2, %3) : (i8, i8) -> i8
    %2 = \"seq.firreg\"(%4, %1) <{\"name\" = \"q\"}> : (i8, !seq.clock) -> i8
    \"hw.output\"(%2) : (i8) -> ()
  }) : () -> ()
}) : () -> ()"

private def testRefusals : String := Id.run do
  let two : Array RuntimeValue := #[i 1 0, i 1 0]
  let four : Array RuntimeValue := #[i 1 0, i 1 0, i 2 0, i 8 0]
  -- Controls: the unaltered modules do simulate.
  if (run counter [(0, two)]).isNone then return "the plain counter stopped simulating"
  if (run mem1 [(0, four)]).isNone then return "the plain memory stopped simulating"
  -- A register whose reset is asynchronous, or that powers up at something other than zero.
  if (run counterAsync [(0, two)]).isSome then return "isAsync was simulated anyway"
  if (run counterPreset [(0, two)]).isSome then return "preset was simulated anyway"
  -- A memory with a latency the driver does not model.
  if (run memBadLatency [(0, four)]).isSome then return "readLatency = 1 was simulated anyway"
  if (run memWuwNew [(0, four)]).isSome then return "wuw = new was simulated anyway"
  -- A clock this driver cannot trace back to a port.
  if (run derivedClock [(0, two)]).isSome then return "a gated clock was simulated anyway"
  return "ok"

/-- info: "ok" -/
#guard_msgs in
#eval! testRefusals

/-! ### A use before definition is refused rather than read as zero

One forward pass settles a netlist only because the sole backward references are register
outputs, which are seeded from state before the pass. A graph region permits others, and a driver
that initialised its value array to zeros would quietly settle them to a fixed point.

Two tests, because they are caught by different things and a mutation run showed it. The
combinational cycle below is refused by the **width discipline**: an undefined value reads as the
zero-width sentinel, and every `comb` operation checks its operand widths, so the cycle fails to
evaluate before `defined` is consulted at all. Removing `defined` leaves it passing.

`testForwardOperand` is the case that `defined` alone catches: a `seq.firmem.write_port`'s data
operand is not width-checked against anything -- it is pushed into the pending write as it comes --
so without `defined` the sentinel is stored in the memory and read back later as a value.
-/

private def combLoop : String :=
"\"builtin.module\"() ({
^bb0():
  \"hw.module\"() <{module_type = !hw.modty<input a : i8, output y : i8>, parameters = [], per_port_attrs = [], sym_name = \"combLoop\"}> ({
  ^bb1(%arg0: i8):
    %0 = \"comb.add\"(%1, %arg0) : (i8, i8) -> i8
    %1 = \"comb.add\"(%0, %arg0) : (i8, i8) -> i8
    \"hw.output\"(%1) : (i8) -> ()
  }) : () -> ()
}) : () -> ()"

private def testCombLoop : String := Id.run do
  match parseModule combLoop with
  | none => return "the loop module did not parse, so this tests nothing"
  | some (ctx, hwModule) =>
    match Netlist.Info.of ctx hwModule with
    | none => return "Info.of rejected it, so settle was never reached"
    | some info =>
      match Netlist.State.init ctx info with
      | none => return "State.init rejected it"
      | some st =>
        if (Netlist.settle ctx info #[i 8 1] st).isSome then
          return "a combinational cycle settled to a value"
        return "ok"

/-- info: "ok" -/
#guard_msgs in
#eval! testCombLoop

/-- A `seq.firmem.write_port` whose data operand is defined below it. Legal in a graph region, and
nothing about the write port's shape is wrong -- only the order. -/
private def forwardOperand : String :=
"\"builtin.module\"() ({
^bb0():
  \"hw.module\"() <{module_type = !hw.modty<input clk : i1, input addr : i2, input we : i1, input din : i8, output dout : i8>, parameters = [], per_port_attrs = [], sym_name = \"forwardOperand\"}> ({
  ^bb1(%arg0: i1, %arg1: i2, %arg2: i1, %arg3: i8):
    %0 = \"seq.to_clock\"(%arg0) : (i1) -> !seq.clock
    %1 = \"seq.firmem\"() <{\"name\" = \"mem\", \"readLatency\" = 0 : i32, \"writeLatency\" = 1 : i32, \"ruw\" = 1 : i32, \"wuw\" = 1 : i32}> : () -> !seq.firmem<4 x 8>
    \"seq.firmem.write_port\"(%1, %arg1, %0, %arg2, %3) <{\"operandSegmentSizes\" = array<i32: 1, 1, 1, 1, 1, 0>}> : (!seq.firmem<4 x 8>, i2, !seq.clock, i1, i8) -> ()
    %3 = \"comb.add\"(%arg3, %arg3) : (i8, i8) -> i8
    %2 = \"seq.firmem.read_port\"(%1, %arg1, %0) : (!seq.firmem<4 x 8>, i2, !seq.clock) -> i8
    \"hw.output\"(%2) : (i8) -> ()
  }) : () -> ()
}) : () -> ()"

private def testForwardOperand : String := Id.run do
  match parseModule forwardOperand with
  | none => return "the module did not parse, so this tests nothing"
  | some (ctx, hwModule) =>
    match Netlist.Info.of ctx hwModule with
    | none => return "Info.of rejected it, so settle was never reached"
    | some info =>
      match Netlist.State.init ctx info with
      | none => return "State.init rejected it"
      | some st =>
        -- clk, addr, we, din
        if (Netlist.settle ctx info #[i 1 0, i 2 0, i 1 1, i 8 7] st).isSome then
          return "an operand used before its definition was read as a value"
        return "ok"

/-- info: "ok" -/
#guard_msgs in
#eval! testForwardOperand

/-- The control: the same module with the `comb.add` moved above the write port. Nothing else
differs, so the refusal above is about the operand order and not about the module's shape. -/
private def forwardOperandFixed : String :=
  forwardOperand.replace
    "    \"seq.firmem.write_port\"(%1, %arg1, %0, %arg2, %3) <{\"operandSegmentSizes\" = array<i32: 1, 1, 1, 1, 1, 0>}> : (!seq.firmem<4 x 8>, i2, !seq.clock, i1, i8) -> ()\n    %3 = \"comb.add\"(%arg3, %arg3) : (i8, i8) -> i8"
    "    %3 = \"comb.add\"(%arg3, %arg3) : (i8, i8) -> i8\n    \"seq.firmem.write_port\"(%1, %arg1, %0, %arg2, %3) <{\"operandSegmentSizes\" = array<i32: 1, 1, 1, 1, 1, 0>}> : (!seq.firmem<4 x 8>, i2, !seq.clock, i1, i8) -> ()"
  |>.replace "\"forwardOperand\"" "\"forwardOperandFixed\""

private def testForwardOperandControl : String := Id.run do
  -- Writing 7+7 = 14 to address 0, then reading it back.
  let wr : Array RuntimeValue := #[i 1 0, i 2 0, i 1 1, i 8 7]
  let rd : Array RuntimeValue := #[i 1 0, i 2 0, i 1 0, i 8 0]
  match run forwardOperandFixed [(0, wr), (0, rd)] with
  | none => return "the correctly ordered module did not simulate"
  | some trace => if trace != [#[14], #[14]] then return s!"ordered {trace}"
  return "ok"

/-- info: "ok" -/
#guard_msgs in
#eval! testForwardOperandControl

/-! ### `Info.of` is about a `hw.module`

Handed anything else -- the enclosing `builtin.module`, say -- it must decline rather than find no
operations and report an empty netlist, which would simulate as a module with no outputs.
-/

private def testInfoOfRejects : String := Id.run do
  match Veir.Input.parseSourceString counter.toUTF8 "test" with
  | .error _ => return "the counter did not parse"
  | .ok (ctx, top, _) =>
    if (Netlist.Info.of ctx top).isSome then return "Info.of accepted the builtin.module"
    -- Control: it does accept the hw.module inside.
    match parseModule counter with
    | none => return "could not reach the hw.module"
    | some (ctx', hwModule) =>
      if (Netlist.Info.of ctx' hwModule).isNone then return "Info.of rejected the hw.module"
      return "ok"

/-- info: "ok" -/
#guard_msgs in
#eval! testInfoOfRejects

/-! ### A read port's optional enable

`seq.firmem.read_port` takes its `enable` last and optional, which is why it carries no
`operandSegmentSizes`. With the operand present and low the port reads poison, not the stored
word and not zero -- and `run` reports a poison output as a refusal, so the two are told apart by
reading the value directly.
-/

private def memEnabledRead : String :=
"\"builtin.module\"() ({
^bb0():
  \"hw.module\"() <{module_type = !hw.modty<input clk : i1, input we : i1, input addr : i2, input din : i8, input re : i1, output dout : i8>, parameters = [], per_port_attrs = [], sym_name = \"memEnabledRead\"}> ({
  ^bb1(%arg0: i1, %arg1: i1, %arg2: i2, %arg3: i8, %arg4: i1):
    %0 = \"seq.to_clock\"(%arg0) : (i1) -> !seq.clock
    %1 = \"seq.firmem\"() <{\"name\" = \"mem\", \"readLatency\" = 0 : i32, \"writeLatency\" = 1 : i32, \"ruw\" = 1 : i32, \"wuw\" = 1 : i32}> : () -> !seq.firmem<4 x 8>
    %2 = \"seq.firmem.read_port\"(%1, %arg2, %0, %arg4) : (!seq.firmem<4 x 8>, i2, !seq.clock, i1) -> i8
    \"seq.firmem.write_port\"(%1, %arg2, %0, %arg1, %arg3) <{\"operandSegmentSizes\" = array<i32: 1, 1, 1, 1, 1, 0>}> : (!seq.firmem<4 x 8>, i2, !seq.clock, i1, i8) -> ()
    \"hw.output\"(%2) : (i8) -> ()
  }) : () -> ()
}) : () -> ()"

/-- Settle once with the given inputs and report the output port, distinguishing poison from a
value and both from a refusal. -/
private def readOut (text : String) (args : Array RuntimeValue) : Option (Option Nat) := do
  let (ctx, hwModule) ← parseModule text
  let info ← Netlist.Info.of ctx hwModule
  let st ← Netlist.State.init ctx info
  let (vals, _) ← Netlist.settle ctx info args st
  let outs ← Netlist.outputs ctx info vals
  match (outs[0]? : Option RuntimeValue) with
  | some (.int _ (.val b)) => some (some b.toNat)
  | some (.int _ .poison) => some none
  | _ => none

private def testReadEnable : String := Id.run do
  -- clk, we, addr, din, re
  let enabled : Array RuntimeValue := #[i 1 0, i 1 0, i 2 0, i 8 0, i 1 1]
  let disabled : Array RuntimeValue := #[i 1 0, i 1 0, i 2 0, i 8 0, i 1 0]
  match readOut memEnabledRead enabled with
  | none => return "the enabled read did not simulate"
  | some none => return "the enabled read gave poison"
  | some (some v) => if v != 0 then return s!"the enabled read gave {v}"
  match readOut memEnabledRead disabled with
  | none => return "the disabled read did not simulate"
  | some (some v) => return s!"the disabled read gave {v} rather than poison"
  | some none => return "ok"

/-- info: "ok" -/
#guard_msgs in
#eval! testReadEnable

/-! ### A module with no state at all

No registers, no memories, so `Info.regs` and `Info.mems` are empty and `stepClock` has nothing to
fire. It must still settle and produce outputs rather than divide by the number of registers, so
to speak.
-/

private def pureComb : String :=
"\"builtin.module\"() ({
^bb0():
  \"hw.module\"() <{module_type = !hw.modty<input a : i4, input b : i4, output y : i8>, parameters = [], per_port_attrs = [], sym_name = \"pureComb\"}> ({
  ^bb1(%arg0: i4, %arg1: i4):
    %0 = \"comb.concat\"(%arg0, %arg1) : (i4, i4) -> i8
    \"hw.output\"(%0) : (i8) -> ()
  }) : () -> ()
}) : () -> ()"

private def testPureComb : String := Id.run do
  if readOut pureComb #[i 4 10, i 4 3] != some (some 163) then return "settle"
  -- And a clock tick on a module with no clock changes nothing rather than failing.
  match run pureComb [(0, #[i 4 10, i 4 3])] with
  | none => return "stepClock refused a module with no registers"
  | some trace => if trace != [#[163]] then return s!"stepClock {trace}"
  return "ok"

/-- info: "ok" -/
#guard_msgs in
#eval! testPureComb

/-! ### The argument count is checked

`settle` is handed the module's inputs positionally, so a caller that passes the wrong number is
making an error no type catches.
-/

private def testArgCount : String := Id.run do
  match parseModule counter with
  | none => return "the counter did not parse"
  | some (ctx, hwModule) =>
    match Netlist.Info.of ctx hwModule with
    | none => return "Info.of rejected the counter"
    | some info =>
      match Netlist.State.init ctx info with
      | none => return "State.init rejected the counter"
      | some st =>
        if (Netlist.settle ctx info #[i 1 0] st).isSome then return "one argument was accepted"
        if (Netlist.settle ctx info #[i 1 0, i 1 0, i 1 0] st).isSome then
          return "three arguments were accepted"
        if (Netlist.settle ctx info #[i 1 0, i 1 0] st).isNone then
          return "two arguments were refused"
        return "ok"

/-- info: "ok" -/
#guard_msgs in
#eval! testArgCount
