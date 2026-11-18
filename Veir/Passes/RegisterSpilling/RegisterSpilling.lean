module

public import Veir.Pass
import Veir.Passes.RegisterAllocation.Helper
import Veir.Rewriter.WfRewriter
import Std.Data.HashSet

namespace Veir

namespace RegisterSpilling

/-!
  Pass that ensure that all blocks can be allocated in `numberRegisters` (currently hardcoded to 28) registers by inserting loads and stores.

  High-level algorithm for each basic block:
  1. Do backwards walk on block and record for every op which SSA values are last used ("die" at that op)
  2. Do forward walk on block.
     state.loadedValues holds SSA values that are currently in a register, ordered by when they were loaded (oldest first)
     state.slots: Map from SSA value that was spilled to the new SSA value that is returned by the alloca op that was used to put the original value on the stack
     For every op:
     2.1 Check if (loadedValues union srcOperands) are larger than number of available registers
         If so, evict the loadedValues that were loaded first (FIFO) (not values that are used as operands!) to memory
     2.2 Check if all operands are in loadedValues.
         If not, insert load operations (throw error if there is no slot that holds the value)
     2.3 Check which SSA values are last used at an op. Remove them from loadedValues
     2.4 Check if (loadedValues union opResults) are larger than number of available registers
         If so, evict the loadedValues that were loaded first (FIFO) (not values that are used as operands!) to memory
-/

/-- The spiller's state while walking a block forward. -/
structure SpillState where
  /--  Values currently assumed to be in a register, in the order they were loaded,
  meaning the value at `loadedValues[0]` has been in the register file the longest.   -/
  loadedValues : Array ValuePtr := #[]
  /-- The stack slot (alloca result) of every value spilled so far. -/
  slots : Std.HashMap ValuePtr ValuePtr := ∅
  /-- For a reloaded value, the `ld` result that currently holds it. -/
  current : Std.HashMap ValuePtr ValuePtr := ∅

/--
  Spill `value` to risc.stack with alloca. insert that operation before op
-/
def insertSpill (ctx : WfIRContext OpCode) (op : OperationPtr) (value: ValuePtr):
    Except String (WfIRContext OpCode × ValuePtr) := do
  let some (ctx, alloca) := WfRewriter.createOp! ctx Riscv_Stack.alloca
      #[RegisterType.mk] #[] #[] #[]
      ({ size := 8, alignment := 8 } : RISCVStackAllocaProperties)
      (some (.before op))
    | throw "register spilling could not create a stack slot"
  let slot : ValuePtr := alloca.getResult 0
  let some (ctx, _) := WfRewriter.createOp! ctx Riscv.sd
      #[] #[value, slot] #[] #[]
      ({ value := 0, volatile_ := false } : RISCVMemProperties)
      (some (.before op))
    | throw "register spilling could not create a spill store"
  return (ctx, slot)

/--
Evict `value` from the registers before `op`: store it to a fresh slot unless it already has
one, in which case the slot still holds it and no store is needed.
-/
def evictValue (ctx : WfIRContext OpCode) (state : SpillState) (op : OperationPtr)
    (value : ValuePtr) : Except String (WfIRContext OpCode × SpillState) := do
  let state := { state with loadedValues := state.loadedValues.erase value }
  if state.slots.contains value then return (ctx, state)
  let (ctx, slot) ← insertSpill ctx op value
  return (ctx, { state with slots := state.slots.insert value slot })

/--
Evict loaded values until all values `needed` by `op` fit in the registers.
FIFO is used for evicting from the `loadedValues`. Values in `needed` are never evicted.
-/
def evict (ctx : WfIRContext OpCode) (state : SpillState) (op : OperationPtr)
    (needed : Std.HashSet ValuePtr) (numRegisters : Nat) :
    Except String (WfIRContext OpCode × SpillState) := do
  let evictable := state.loadedValues.filter (!needed.contains ·)
  let numberToEvict := needed.size + evictable.size - numRegisters
  if evictable.size < numberToEvict then
    throw s!"register spilling: operation needs more than {numRegisters} registers"
  -- Future work: choose better eviction heuristic than FIFO
  let mut ctx := ctx
  let mut state := state
  for value in evictable.take numberToEvict do
    (ctx, state) ← evictValue ctx state op value
  return (ctx, state)

/--
Reload the value stored in `slot` before `op`. The operands of `op` are left as they are;
the slot map records where the value lives.
-/
def insertReload (ctx : WfIRContext OpCode) (op : OperationPtr) (slot : ValuePtr) :
    Except String (WfIRContext OpCode × ValuePtr) := do
  let some (ctx, ld) := WfRewriter.createOp! ctx Riscv.ld
      #[RegisterType.mk] #[slot] #[] #[]
      ({ value := 0, volatile_ := false } : RISCVMemProperties)
      (some (.before op))
    | throw "register spilling could not create a reload"
  return (ctx, (ld.getResult 0))

/--
Spill around one operation, as described in the module docstring: evict to make room for
the operands that must be reloaded, reload them, free the operands that die here, and make
room for the results.
-/
def spillOp (ctx : WfIRContext OpCode) (state : SpillState)
    (lastUses : Std.HashMap OperationPtr (Std.HashSet ValuePtr)) (numRegisters : Nat)
    (op : OperationPtr) : Except String (WfIRContext OpCode × SpillState) := do
  let mut ctx := ctx
  let mut state := state

  let operands := Std.HashSet.ofArray (op.getOperands! ctx.raw)

  -- evict enough values that all operands fit into registers
  (ctx, state) <- evict ctx state op operands numRegisters

  -- Reload operands, if needed
  for value in op.getOperands! ctx.raw do
    if state.loadedValues.contains value then continue
    let some slot := state.slots[value]?
      | throw "register spilling found an operand that is neither in a register nor spilled"
    let (ctx', reloaded) ← insertReload ctx op slot
    ctx := ctx'
    state := { state with
              loadedValues := state.loadedValues.push value
              current := state.current.insert value reloaded }

  -- Point the operands of `op` at their reloaded copies.
  for i in [0:op.getNumOperands! ctx.raw] do
    let value := op.getOperand! ctx.raw i
    if let some reloaded := state.current[value]? then
      ctx := WfRewriter.replaceOperand! ctx (op.getOpOperand i) reloaded

  -- Operands used for the last time free their registers.
  for value in lastUses.getD op ∅ do
    state := { state with loadedValues := state.loadedValues.erase value }

  -- evict enough values that all results fit into registers
  let results := Std.HashSet.ofArray (op.getResults! ctx.raw)
  (ctx, state) <- evict ctx state op results numRegisters

  -- add results to loadedValues (if they have uses, otherwise they can just be discarded)
  for result in op.getResults! ctx.raw do
    if result.hasUses! ctx.raw then
      state := { state with loadedValues := state.loadedValues.push result }

  return (ctx, state)

/--
Spill around `op` and every operation after it in its block, walking forward.
-/
partial def spillOps (ctx : WfIRContext OpCode) (state : SpillState)
    (lastUses : Std.HashMap OperationPtr (Std.HashSet ValuePtr)) (numRegisters : Nat) :
    Option OperationPtr → Except String (WfIRContext OpCode × SpillState)
  | none => return (ctx, state)
  | some op => do
    let (ctx, state) ← spillOp ctx state lastUses numRegisters op
    spillOps ctx state lastUses numRegisters (op.getNextOp! ctx.raw)

/--
Backwards walk to record last time any value is used
-/
partial def lastUsesFrom (ctx : WfIRContext OpCode) (op : Option OperationPtr)
    (seenValues : Std.HashSet ValuePtr) (lastUses : Std.HashMap OperationPtr (Std.HashSet ValuePtr)) :
    Std.HashMap OperationPtr (Std.HashSet ValuePtr) :=
  match op with
  | none => lastUses
  | some op =>
    let operands := op.getOperands! ctx.raw
    let dyingOperands := Std.HashSet.ofArray (operands.filter (!seenValues.contains ·))
    lastUsesFrom ctx (op.getPrevOp! ctx.raw) (seenValues.insertMany operands) (lastUses.insert op dyingOperands)

/--
Spill the values of `block` so that at most `numRegisters` are in registers at any point.
Return the context with the spill code inserted and, for every spilled value, its slot.
-/
def spillBlock (ctx : WfIRContext OpCode) (block : BlockPtr)
    (numRegisters : Nat) :
    Except String (WfIRContext OpCode × Std.HashMap ValuePtr ValuePtr) := do
  -- Walk the operations in reverse and store for every operation the values that die there.
  let lastUses := lastUsesFrom ctx (block.getLastOp! ctx.raw) ∅ ∅
  let (ctx, state) ← spillOps ctx {} lastUses numRegisters (block.getFirstOp! ctx.raw)
  return (ctx, state.slots)

end RegisterSpilling

/-- RV64 has 32 registers, but we don't allocate x0 (zero), x1 (ra), x3 (gp) and x4 (tp)
TODO: As spilling is integrated with the register allocation pass and calling convention/ control flow is supported, this will become a dynamic value  -/
def rv64NumRegisters : Nat := 28

def RegisterSpillingPass.impl (ctx : WfIRContext OpCode) (op : OperationPtr)
  (_ : op.InBounds ctx.raw) : ExceptT String IO (WfIRContext OpCode) := do
  let entries ← allocatableBlocks ctx op
  let mut ctx := ctx
  for entry in entries do
      (ctx, _) ← RegisterSpilling.spillBlock ctx entry rv64NumRegisters
  return ctx

public def RegisterSpillingPass : Pass OpCode :=
  { name := "register-spilling-riscv64"
    description := "Spill values to the stack to ensure the number of live values never exceeds the number of registers."
    run := fun _ => RegisterSpillingPass.impl }

end Veir
