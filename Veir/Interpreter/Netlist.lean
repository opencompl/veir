module

public import Veir.Interpreter.Basic
public import Veir.Dialects.Seq.OpInfo
public import Veir.Dialects.HW.OpInfo

namespace Veir.Netlist

public section

/-! # Simulating a `hw.module`

A synchronous netlist, not a control-flow graph. `Veir.Interpreter.CTreeInterpreter` walks blocks
and terminators because that is what `func`, `llvm` and `riscv` are; a `hw.module` has one block,
no terminator worth branching on, and a *clock*. Its evaluation model is different enough to want
its own driver:

* **settle** -- evaluate every operation once, in order, to get the combinational values implied by
  the current register contents and input values;
* **clock edge** -- every `seq.firreg` on the clock being ticked takes whatever its input settled
  to, and every enabled `seq.firmem.write_port` on that clock lands;
* **settle again**, so the outputs reflect the registers as they now are.

### Why one forward pass settles

`hw.module` is a graph region, so an operation may use a value defined below it, and real lowerings
rely on that: the logic computing a register's input refers to the register's own output. But a
register's output is *state* -- it is read from `State`, not computed -- so seeding the register
results before the pass makes every remaining use a backward reference. One pass in program order
is then enough, and no fixpoint iteration is needed.

This is a property of how the module is written rather than of MLIR, which would happily accept a
combinational cycle. `settle` returns `none` on a use that has not been defined yet, so such a
module is refused rather than silently read as zero.

### State is arrays, not `VariableState`

`OperationPtr` is a dense `Nat` and every operation here has at most one result, so values live in
an `Array RuntimeValue` indexed by operation id. `VariableState` -- a hash map carrying proof
fields with a `Conforms` check on every write -- is the right structure for an interpreter that
must stay well-formed across arbitrary rewrites, and the wrong one for a loop that runs a few
hundred thousand times inside a `native_decide`.

### What is refused rather than approximated

`ruw` other than `old`, `wuw` other than `port_order`, `seq.firmem.read_write_port`, an
asynchronous reset, and a `preset`. Each is a real CIRCT behaviour this driver does not model, and
returning `none` is what keeps a caller from proving something about a module whose meaning it got
wrong.
-/

/-- `ruw = old`: a read sees the memory as it was before this cycle's writes. -/
private def ruwOld : Int := 1
/-- `wuw = port_order`: two writes to one address in a cycle land in port order. -/
private def wuwPortOrder : Int := 1

/-- A `seq.firmem.write_port` that the settled values enabled, to be applied at the edge. -/
structure WriteReq where
  /-- `OperationPtr.id` of the `seq.firmem` being written. -/
  mem : Nat
  addr : Nat
  data : RuntimeValue
  /-- Block argument index of the clock this port is tied to. -/
  clock : Nat

/-- The contents of a module's state elements.

Both arrays are indexed by `OperationPtr.id` and are therefore sparse: entries that do not
correspond to a `seq.firreg` or a `seq.firmem` are never read. That costs a little memory and
buys O(1) access without hashing. -/
structure State where
  regs : Array RuntimeValue
  mems : Array (Array RuntimeValue)
deriving Inhabited

/-- One operation, with everything `settle` needs about it read out of the arena in advance.

Re-reading an operation's opcode, operand list and result types on every tick is what made a first
version of this driver several times slower than a hand-written netlist interpreter: those are
array allocations per operation per settle, and a settle runs hundreds of thousands of times
inside a `native_decide`. The IR stays the source of truth; this is a plan derived from it. -/
structure OpStep where
  op : OperationPtr
  opType : OpCode
  operands : Array ValuePtr
  resultTypes : Array TypeAttr
  numResults : Nat
deriving Inhabited

/-- What a module's structure is, computed once rather than per tick.

Re-walking the operation linked list, re-reading each `seq.firmem`'s shape and re-tracing each
register's clock on every tick would dominate the cost of simulating a small design. -/
structure Info where
  /-- The `hw.module`'s single block. -/
  block : BlockPtr
  /-- Its operations, in program order, with their arena data already read. -/
  ops : Array OpStep
  /-- The `seq.firreg` operations, and for each the block argument index of its clock. -/
  regs : Array (OperationPtr × Nat)
  /-- The `seq.firmem` operations, with the shape each declares. -/
  mems : Array (OperationPtr × Seq.FirMemType)
  /-- The `hw.output` terminator, whose operands are the module's results. -/
  output : Option OperationPtr
  numArgs : Nat
  /-- One past the highest operation id, so an array can be sized. -/
  numValues : Nat
deriving Inhabited

/-! ### Reading the module's structure -/

/-- Follow a `!seq.clock` value back to the module input driving it.

A clock reaches a register through a `seq.to_clock` whose operand is a block argument, which is
the only shape a lowering can produce for a module that takes its clock as a port. Anything else
-- a gated or derived clock -- is refused here rather than guessed at. -/
private def resolveClock (ctx : WfIRContext OpCode) (v : ValuePtr) : Option Nat := do
  let .opResult ⟨toClockOp, _⟩ := v | none
  let .seq .to_clock := toClockOp.getOpType! ctx.raw | none
  let operands := toClockOp.getOperands! ctx.raw
  let some (v0 : ValuePtr) := operands[0]? | none
  let .blockArgument ⟨_, idx⟩ := v0 | none
  return idx

/-- The `!seq.firmem` an operand refers to, as the id of the `seq.firmem` that declared it. -/
private def resolveMem (ctx : WfIRContext OpCode) (v : ValuePtr) : Option Nat := do
  let .opResult ⟨memOp, _⟩ := v | none
  let .seq .firmem := memOp.getOpType! ctx.raw | none
  return memOp.id

/-- The properties a memory port operation was given, rejecting the modes this driver does not
model. See the header. -/
private def checkFirMem (ctx : WfIRContext OpCode) (memOp : OperationPtr) : Option Unit := do
  let .seq .firmem := memOp.getOpType! ctx.raw | none
  let props := memOp.getProperties! ctx.raw (OpCode.seq Seq.firmem)
  if props.ruw.value != ruwOld then none
  if props.wuw.value != wuwPortOrder then none
  if props.readLatency.value != 0 then none
  if props.writeLatency.value != 1 then none
  return ()

/-- Collect a `hw.module`'s structure. Call once per module, not once per tick. -/
def Info.of (ctx : WfIRContext OpCode) (hwModule : OperationPtr) : Option Info := do
  let .hw .module := hwModule.getOpType! ctx.raw | none
  if hwModule.getNumRegions! ctx.raw != 1 then none
  let region := hwModule.getRegion! ctx.raw 0
  let some block := region.getFirstBlock! ctx.raw | none
  let mut ops : Array OpStep := #[]
  let mut regs : Array (OperationPtr × Nat) := #[]
  let mut mems : Array (OperationPtr × Seq.FirMemType) := #[]
  let mut output : Option OperationPtr := none
  let mut numValues := 0
  let mut cur := block.getFirstOp! ctx.raw
  -- The operation list is a linked list; `ops.size` bounds the walk so this stays structural.
  for _ in List.range (ctx.raw.operations.size + 1) do
    match cur with
    | none => break
    | some op =>
      let opType := op.getOpType! ctx.raw
      ops := ops.push { op, opType, operands := op.getOperands! ctx.raw,
                        resultTypes := op.getResultTypes! ctx.raw,
                        numResults := op.getNumResults! ctx.raw }
      numValues := max numValues (op.id + 1)
      match opType with
      | .seq .firreg =>
        let props := op.getProperties! ctx.raw (OpCode.seq Seq.firreg)
        -- An asynchronous reset fires off the clock entirely, and a `preset` starts the register
        -- somewhere other than zero. Neither is modelled; see the header.
        if props.isAsync then none
        if props.preset.isSome then none
        let operands := op.getOperands! ctx.raw
        let some clockVal := operands[1]? | none
        let some clockArg := resolveClock ctx clockVal | none
        regs := regs.push (op, clockArg)
      | .seq .firmem =>
        let some resType := (op.getResultTypes! ctx.raw)[0]? | none
        let .seqFirMemType memType := resType.val | none
        -- Checked here rather than in `settle`: it is a property of the module, and `settle` runs
        -- hundreds of thousands of times.
        checkFirMem ctx op
        mems := mems.push (op, memType)
      | .hw .output => output := some op
      | _ => pure ()
      cur := op.getNextOp! ctx.raw
  return { block, ops, regs, mems, output,
           numArgs := block.getNumArguments! ctx.raw, numValues }

/-- Every register at zero and every memory zero-filled, which is what CIRCT leaves a `seq.firreg`
with no `preset` and a `seq.firmem` at. -/
def State.init (ctx : WfIRContext OpCode) (info : Info) : Option State := do
  let mut regs : Array RuntimeValue := Array.replicate info.numValues (.int 0 (.val (BitVec.ofNat 0 0)))
  for (op, _) in info.regs do
    let some resType := (op.getResultTypes! ctx.raw)[0]? | none
    let .integerType bw := resType.val | none
    regs := regs.setIfInBounds op.id (.int bw.bitwidth (.val (BitVec.ofNat bw.bitwidth 0)))
  let mut mems : Array (Array RuntimeValue) := Array.replicate info.numValues #[]
  for (op, memType) in info.mems do
    mems := mems.setIfInBounds op.id
      (Array.replicate memType.depth (.int memType.width (.val (BitVec.ofNat memType.width 0))))
  return { regs, mems }

/-! ### Settling -/

/-- Evaluate every operation once, in program order.

Returns the value of each operation's first result, indexed by operation id, together with the
writes the settled values enabled. Register results are *seeded* from `st` rather than computed --
that is what makes them state, and what makes one forward pass sufficient. -/
def settle (ctx : WfIRContext OpCode) (info : Info) (args : Array RuntimeValue) (st : State) :
    Option (Array RuntimeValue × Array WriteReq) := do
  if args.size != info.numArgs then none
  -- A separate `defined` array rather than `Array (Option RuntimeValue)`: a use before definition
  -- must still be refused -- in a graph region that is a real possibility and a real bug -- but
  -- wrapping every value in an `Option` allocates once per operation per settle, and a settle runs
  -- hundreds of thousands of times inside a `native_decide`.
  let mut vals : Array RuntimeValue := Array.replicate info.numValues (.int 0 (.val (BitVec.ofNat 0 0)))
  let mut defined : Array Bool := Array.replicate info.numValues false
  for (op, _) in info.regs do
    let some rv := st.regs[op.id]? | none
    vals := vals.setIfInBounds op.id rv
    defined := defined.setIfInBounds op.id true
  let mut writes : Array WriteReq := #[]

  let read (vals : Array RuntimeValue) (defined : Array Bool) (v : ValuePtr) :
      Option RuntimeValue :=
    match v with
    | .blockArgument ⟨_, idx⟩ => args[idx]?
    | .opResult ⟨op, _⟩ => if defined[op.id]! then vals[op.id]? else none

  for step in info.ops do
    let op := step.op
    let opType := step.opType
    let operands := step.operands
    match opType with
    -- Already seeded; its input is read at the edge, not here.
    | .seq .firreg => pure ()
    -- Declares a memory. Its contents are in `st`, and it has no integer value.
    -- Declares a memory. Its contents are in `st`, it has no integer value, and its modes were
    -- checked when `Info` was read.
    | .seq .firmem => pure ()
    | .seq .to_clock =>
      -- Carried through so a register's clock operand resolves, though nothing reads its value.
      let some v := operands[0]? | none
      let some cv := read vals defined v | none
      vals := vals.setIfInBounds op.id cv
      defined := defined.setIfInBounds op.id true
    | .seq .firmem__read_port =>
      let some memV := operands[0]? | none
      let some memId := resolveMem ctx memV | none
      let some addrV := operands[1]? | none
      let some addr := read vals defined addrV | none
      let .int _ (.val addrBits) := addr | none
      -- An enable operand, when present, is the port's third operand after the clock. It is
      -- optional and last, which is why a read port carries no `operandSegmentSizes`.
      let enabled : Bool ←
        match operands[3]? with
        | none => some true
        | some enV =>
          match read vals defined enV with
          | some (.int 1 (.val enBits)) => some (enBits == 1#1)
          | _ => none
      let some contents := st.mems[memId]? | none
      let some word := contents[addrBits.toNat]? | none
      -- `ruw = old`: this reads `st`, which this cycle's writes have not touched.
      let some resType := step.resultTypes[0]? | none
      let .integerType bw := resType.val | none
      vals := vals.setIfInBounds op.id (if enabled then word else .int bw.bitwidth .poison)
      defined := defined.setIfInBounds op.id true
    | .seq .firmem__write_port =>
      let some memV := operands[0]? | none
      let some memId := resolveMem ctx memV | none
      let some addrV := operands[1]? | none
      let some addr := read vals defined addrV | none
      let .int _ (.val addrBits) := addr | none
      let some clockV := operands[2]? | none
      let some clockArg := resolveClock ctx clockV | none
      let some enV := operands[3]? | none
      let enabled : Bool ←
        match read vals defined enV with
        | some (.int 1 (.val enBits)) => some (enBits == 1#1)
        | _ => none
      let some dataV := operands[4]? | none
      let some data := read vals defined dataV | none
      if enabled then
        writes := writes.push { mem := memId, addr := addrBits.toNat, data, clock := clockArg }
    -- Not modelled; see the header.
    | .seq .firmem__read_write_port => none
    -- The terminator carries the module's results and computes nothing. Listed before the
    -- general `hw` case below, which would otherwise try to evaluate it.
    | .hw .output => pure ()
    -- `comb` and `hw` are dispatched directly rather than through `Veir.interpretOp'`. That
    -- function is one match over every dialect, so referring to it makes a netlist depend on the
    -- LLVM memory model -- which showed up as two extra `bv_decide` axioms under `#print axioms`
    -- for theorems that never load a byte. Naming the two dialects a netlist can contain costs
    -- nothing and refuses the rest, which is the right answer for an `llvm.add` in a `hw.module`
    -- anyway.
    | .comb combOp =>
      let some operandVals := operands.mapM (read vals defined) | none
      let some (results, _) := Comb.interpretOp' combOp
        (op.getProperties! ctx.raw (OpCode.comb combOp))
        step.resultTypes operandVals #[] | none
      if step.numResults > 0 then
        let some r := results[0]? | none
        vals := vals.setIfInBounds op.id r
        defined := defined.setIfInBounds op.id true
    | .hw hwOp =>
      let some (results, _) := HW.interpretOp' hwOp
        (op.getProperties! ctx.raw (OpCode.hw hwOp))
        step.resultTypes #[] | none
      if step.numResults > 0 then
        let some r := results[0]? | none
        vals := vals.setIfInBounds op.id r
        defined := defined.setIfInBounds op.id true
    -- A `hw.module` body is `comb`, `hw` and `seq`. Anything else is refused rather than
    -- interpreted: see the comment above.
    | _ => none

  return (vals, writes)

/-- The module's output port values, given settled values. -/
def outputs (ctx : WfIRContext OpCode) (info : Info) (vals : Array RuntimeValue) :
    Option (Array RuntimeValue) := do
  let some outputOp := info.output | none
  (outputOp.getOperands! ctx.raw).mapM fun v =>
    match v with
    | .blockArgument _ => none
    | .opResult ⟨op, _⟩ => vals[op.id]?

/-! ### Taking a clock edge -/

/-- One tick of one clock: settle, take that clock's edge, settle again.

`clock` is the index of the module input carrying it. Registers on *other* clocks, and writes to
memories tied to them, are left alone -- which is what lets two clock domains drift apart, and is
the whole reason a design needs more than one. -/
def stepClock (ctx : WfIRContext OpCode) (info : Info) (clock : Nat)
    (args : Array RuntimeValue) (st : State) : Option State := do
  let (vals, writes) ← settle ctx info args st
  let mut regs := st.regs
  for (op, regClock) in info.regs do
    if regClock == clock then
      let operands := op.getOperands! ctx.raw
      let some inputV := operands[0]? | none
      let some input := (match inputV with
        | .blockArgument ⟨_, idx⟩ => args[idx]?
        | .opResult ⟨defOp, _⟩ => vals[defOp.id]?) | none
      regs := regs.setIfInBounds op.id input
  let mut mems := st.mems
  -- In port order, which is `wuw = port_order`: a later write to the same address wins.
  for w in writes do
    if w.clock == clock then
      let some contents := mems[w.mem]? | none
      if w.addr ≥ contents.size then none
      mems := mems.setIfInBounds w.mem (contents.setIfInBounds w.addr w.data)
  return { regs, mems }

end

end Veir.Netlist
