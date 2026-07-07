import Veir.Prelude
import Veir.IR.Basic
import Veir.Rewriter.Basic
import Veir.GlobalOpInfo
import Veir.Printer

open Veir
open Attribute
set_option maxHeartbeats 100000000
set_option warn.sorry false

-- TODO: the array is bad... We need our own array type or not use arrays
-- set_option trace.Compiler.reduceArity true in
buffed (def_lemma := false)
def createManyOpsLoopSim (ctx : Sim.IRContext OpCode) (insertPoint : InsertPoint)
    (prev2 prev1 : Sim.ValuePtr) (n : Nat) : Option (Sim.IRContext OpCode) :=
  match n with
  | 0 => some ctx
  | n + 1 => do
    let prev2 := ⟨prev2.impl, .blockArgument ⟨⟨0⟩, 0⟩⟩
    let prev1 := ⟨prev1.impl, .blockArgument ⟨⟨0⟩, 0⟩⟩
    match Rewriter.createOp ctx (.arith .addi) #[IntegerType.mk 32] #[prev2, prev1] #[] #[]
        (NswNuwProperties.mk false false) (some insertPoint) sorry sorry sorry sorry sorry sorry with
    | some (ctx, op) =>
      createManyOpsLoopSim ctx insertPoint prev1
        (Sim.ValuePtr.fromOpResultPtr (op.getResultPtr ctx 0 sorry)) n
    | _ => none

#print createManyOpsLoopImpl
#print createManyOpsLoop

-- set_option trace.Compiler.reduceArity true
buffed (def_lemma := false)
def createManyOpsSim (n : Nat) : Option (Sim.BlockPtr × Sim.IRContext OpCode) := do
  -- Top-level `builtin.module` with one region holding a single empty block.
  let some (ctx, topOp) := IRContext.create OpCode
    | none

  let ctx := dumpOp topOp ctx "AFTER creation topOp is"

  -- Reach the module's block and give it one `i32` parameter.
  let region : Sim.RegionPtr := topOp.getRegionPtr ctx 0 sorry sorry
  let ctx := dumpRegion region ctx "AFTER region"
  -- TODO: add a block with two arguments
  let block := (region.getFirstBlock ctx (by sorry)).toOption.get!
  let ctx := dumpRegion region ctx "region"
  let ctx := dumpBlock block ctx "block"

  let insertPoint := InsertPoint.atEnd ⟨block.impl.toNat⟩

  let some (ctx, op) := Rewriter.createOp ctx (.test .test) #[IntegerType.mk 32] #[] #[] #[]
      default (some insertPoint) sorry sorry sorry sorry sorry
    | none
  let ctx := dumpOp op ctx "first op"
  let op := op.getResultPtr ctx 0 (by sorry)

  -- The block parameter, as a value; seeding both `prev2`/`prev1` with it makes the first op
  -- `addi param param`.
  let param : Sim.ValuePtr := .fromOpResultPtr op

  let ctx ← createManyOpsLoop ctx insertPoint param param n
  pure (block, ctx)

buffed (def_lemma := false)
def replaceOps.loopSim (ctx : Sim.IRContext OpCode) (op : Sim.OperationPtr) (depth : UInt64 := -1) :
  Option (Sim.IRContext OpCode) := do
  if depth = 0 then none else
  if (op.getNextOp ctx sorry).impl = .none then
    some ctx
  else
    let nextOp := op.getNextOp ctx (by sorry) |>.toOption.get sorry
    if op.getNumOperands ctx (by sorry) = 2 then
      -- TODO: valueptr etc
      -- let oper := op.getOperandPtr ctx 0 (by sorry)
      -- let prevval := oper.getValue ctx (by sorry)
      -- let some ctx := Rewriter.replaceOp? ctx op prevop sorry sorry sorry sorry | none
      let prevop := op.getPrevOp ctx (by sorry) |>.toOption.get sorry
      let some ctx := Rewriter.replaceOp? ctx op prevop sorry sorry sorry sorry sorry | none
      replaceOps.loopSim ctx nextOp (depth - 1)
    else
      none
partial_fixpoint

buffed (def_lemma := false)
def replaceOpsSim (ctx : Sim.IRContext OpCode) (block : Sim.BlockPtr) : Option (Sim.IRContext OpCode) := do
  let first := block.getFirstOp ctx (by sorry) |>.toOption.get sorry
  let second := first.getNextOp ctx (by sorry) |>.toOption.get sorry
  -- let second := second.getNextOp ctx (by sorry) |>.toOption.get sorry
  -- let op := first.getNextOp ctx (by sorry) |>.toOption.get sorry
  replaceOps.loop ctx second

@[inline]
def check (ctx : Sim.IRContext OpCode) (block : Sim.BlockPtr) : UInt64 := Id.run do
  let first := block.getLastOp ctx (by sorry) |>.toOption.get sorry
  let first := first.getPrevOp ctx (by sorry) |>.toOption.get sorry
  first.impl
  -- (first.getPrevOp ctx (by sorry)).impl

buffed
def blockLength.loopSim (ctx : Sim.IRContext OpCode) (op : Sim.OperationPtr) (count : UInt64 := 0) : UInt64 :=
  let ctx := dumpOp op ctx "blockLength.loopSim"
  match op.getNextOp ctx (by sorry) |>.toOption with
  | none => count
  | some nextOp => blockLength.loopSim ctx nextOp (count + 1)
partial_fixpoint

buffed (def_lemma := false)
def blockLengthSim (ctx : Sim.IRContext OpCode) (block : Sim.BlockPtr) : UInt64 := Id.run do
  let first := block.getFirstOp ctx (by sorry) |>.toOption.get sorry
  blockLength.loop ctx first 0

def main : IO Unit := do
  let N := 10_000_000
  let startTime ← IO.monoNanosNow
  if let some result := createManyOps N then
    let r := result.1
    let endTime ← IO.monoNanosNow
    let elapsed := endTime - startTime |>.toFloat
    let perOp := elapsed / N.toFloat
    let perOpUs := perOp / 1_000
    IO.println s!"Created operation with result: {result.1.impl}, took {perOpUs} μs per operation."
    IO.println s!"Before replacing: {blockLength result.2 r}"
    IO.sleep 100
    let startTime ← IO.monoNanosNow
    if let some result2 := replaceOps result.2 r then
      let endTime ← IO.monoNanosNow
      let elapsed := endTime - startTime |>.toFloat
      IO.sleep 100
      let perOp := elapsed / N.toFloat
      let perOpUs := perOp / 1_000
      IO.println s!"block : {r.impl}"
      IO.println s!"block first: {r.getFirstOp result2 (by sorry) |>.impl}"
      IO.println s!"block last: {r.getLastOp result2 (by sorry) |>.impl}"
      let ctx := dumpOp (r.getFirstOp result2 (by sorry) |>.toOption.get sorry) result2 "first op after replace"
      IO.println s!"Replaced operation with result, took {perOpUs} μs per operation. len {blockLength ctx r}"
  else
    IO.println "Failed to create operations."

-- def printManyOps (n : Nat) : IO Unit := do
--   if let some (ctx, topOp) := createManyOps n then
--     Printer.printModule ctx topOp

-- #eval! printManyOps 5
