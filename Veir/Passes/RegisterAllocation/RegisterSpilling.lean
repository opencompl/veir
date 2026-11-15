module

public import Veir.Pass
public import Veir.Passes.RegisterAllocation.RegisterAllocator
public import Veir.Passes.RegisterAllocation.Helper
public import Veir.Dialects.RISCV.OpInfo
public import Veir.Dialects.RISCV_Stack.OpInfo
public import Std.Data.HashMap
public import Std.Data.HashSet


namespace Veir

public section




namespace RegisterSpilling

/-!
  Pass that ensure that all blocks can be allocated in k registers by inserting loads and stores.

  High-level algorithm for each basic block:
  1. Do backwards walk on block and record for every op which SSA values are last used ("die" at that op)
  2. Do forward walk on block.
     state.loadedValues holds SSA values that are currently in a register
     state.slots: Map from SSA value that was spilled to the new SSA value that is returned by the alloca op that was used to put the original value on the stack
     For every op:
     2.1 Check if (loadedValues union srcOperands) are larger than number of available registers
         If so, evict random currently loadedValues (not values that are used as operands!) to memory
     2.2 Check if all operands are in loadedValues.
         If not, instert load operations (throw error if there is not slot that holds the value)
     2.3 Check which SSA values are last used at an op. Remove them from loadedValues
     2.1 Check if (loadedValues union opResults) are larger than number of available registers
         If so, evict random currently loadedValues (not values that are used as operands!) to memory
-/


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


/-- The spiller's state while walking a block forward. -/
structure SpillState where
  /-- Values currently assumed to be in a register. -/
  loadedValues : Std.HashSet ValuePtr := ∅
  /-- The stack slot (alloca result) of every value spilled so far. -/
  slots : Std.HashMap ValuePtr ValuePtr := ∅

    /-- For a reloaded value, the `ld` result that currently holds it. -/
  current : Std.HashMap ValuePtr ValuePtr := ∅

/--
Evict `value` from the registers before `op`: store it to a fresh slot unless it already has
one, in which case the slot still holds it and no store is needed.
-/
def evict (ctx : WfIRContext OpCode) (state : SpillState) (op : OperationPtr)
    (value : ValuePtr) : Except String (WfIRContext OpCode × SpillState) := do
  let state := { state with loadedValues := state.loadedValues.erase value }
  if state.slots.contains value then return (ctx, state)
  let (ctx, slot) ← insertSpill ctx op value
  return (ctx, { state with slots := state.slots.insert value slot })


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
  let numberToEvict := (state.loadedValues.union operands).size - numRegisters
  let evictable := state.loadedValues.toArray.filter (!operands.contains ·)

  -- Future work: use sensible heuristic for choosing which values to evict
  let chosen := evictable.take numberToEvict
  for valueToEvict in chosen do
    let (ctx', state') <- evict ctx state op valueToEvict
    ctx := ctx'
    state := state'

  -- Reload operands, if needed
  let missing := operands.diff state.loadedValues
  for value in missing do
    let some slot := state.slots[value]?
      | throw "register spilling found an operand that is neither in a register nor spilled"
    let (ctx', reloaded) ← insertReload ctx op slot
    ctx := ctx'
    state := { state with
              loadedValues := state.loadedValues.insert value
              current := state.current.insert value reloaded }

  -- Point the operands of `op` at their reloaded copies.
  for i in [0:op.getNumOperands! ctx.raw] do
    let value := op.getOperand! ctx.raw i
    if let some reloaded := state.current[value]? then
      ctx := WfRewriter.replaceOperand! ctx (op.getOpOperand i) reloaded

  -- Operands used for the last time free their registers.
  for value in lastUses.getD op ∅ do
    state := { state with loadedValues := state.loadedValues.erase value }

  -- Make room for the results, then record them.
  let results := Std.HashSet.ofArray (op.getResults! ctx.raw)

  let numberToEvict := (state.loadedValues.union results).size - numRegisters
  let evictable := state.loadedValues.toArray.filter (!results.contains ·)

  -- Futur work: use sensible heuristic for choosing which values to evict
  let chosen := evictable.take numberToEvict
  for valueToEvict in chosen do
    let (ctx', state') <- evict ctx state op valueToEvict
    ctx := ctx'
    state := state'


  -- add results to loadedValues (if they have uses, otherwise they can just be discarded)
  for result in op.getResults! ctx.raw do
    if result.hasUses! ctx.raw then
      state := { state with loadedValues := state.loadedValues.insert result }

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


/-- The pass entry point: `spillModule`, lifted into the pass monad. -/
def RegisterSpillingPass.impl (ctx : WfIRContext OpCode) (op : OperationPtr)
    (_ : op.InBounds ctx.raw) : ExceptT String IO (WfIRContext OpCode) := do
    let entries ← allocatableBlocks ctx op
    let mut ctx := ctx
    for entry in entries do
        (ctx, _) ← spillBlock ctx entry 20
    return ctx

public def RegisterSpillingPass : Pass OpCode :=
  { name := "register-spilling-riscv64"
    description := "Spill values to the stack so that single-block riscv functions never \
                    have more live values than RV64 allocatable registers."
    run := fun _ => RegisterSpillingPass.impl }
