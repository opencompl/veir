import Veir.Prelude
import Veir.IR.Basic
import Veir.Rewriter.Basic
import Veir.GlobalOpInfo
import Veir.Printer

open Veir
open Attribute
set_option maxHeartbeats 100000000
set_option warn.sorry false

namespace Custom

abbrev Pattern := (Sim.IRContext OpCode) → Sim.OperationPtr → Option (Sim.IRContext OpCode)

-- buffed (def_lemma := false)
def addIConstantFoldingSim (ctx : Sim.IRContext OpCode) (op : Sim.OperationPtr) : Option (Sim.IRContext OpCode) := do
  if op.getOpType ctx sorry ≠ .arith .addi then
    return ctx

  -- Get the lhs and check that it is a constant
  let lhsValuePtr := op.getOperandPtr ctx 0 sorry
  let lhsValue := lhsValuePtr.getValue ctx sorry
  -- Unsafe...
  let lhsOpResultPtr : Sim.OpResultPtr := ⟨lhsValue.impl, sorry⟩
  let lhsOpPtr := lhsOpResultPtr.getOwner ctx sorry

  if lhsOpPtr.getOpType ctx sorry ≠ .arith .constant then
    return ctx

  -- Get the rhs and check that it is a constant
  let rhsValuePtr := op.getOperandPtr ctx 1 sorry
  let rhsValue := rhsValuePtr.getValue ctx sorry
  -- Unsafe...
  let rhsOpResultPtr : Sim.OpResultPtr := ⟨rhsValue.impl, sorry⟩
  let rhsOpPtr := rhsOpResultPtr.getOwner ctx sorry

  if rhsOpPtr.getOpType ctx sorry ≠ .arith .constant then
    return ctx

  -- Get the lhs value
  let lhsAttrs := lhsOpPtr.getAttributes ctx sorry
  let some (attrName, Attribute.integerAttr lhsConstValue) := lhsAttrs.entries[0]? | return ctx
  if lhsConstValue.value ≠ 0 ∨ attrName ≠ "value".toByteArray then
    return ctx

  -- Get the rhs value
  let rhsAttrs := rhsOpPtr.getAttributes ctx sorry
  let some (attrName, Attribute.integerAttr rhsConstValue) := rhsAttrs.entries[0]? | return ctx
  if rhsConstValue.value ≠ 0 ∨ attrName ≠ "value".toByteArray then
    return ctx

  -- Compute the sum
  let sumValue := IntegerAttr.mk (rhsConstValue.value + lhsConstValue.value) (IntegerType.mk 32)
  let insertPoint := InsertPoint.before ⟨op.impl.toNat⟩
  let (ctx, newOp) ← Rewriter.createOp ctx (.arith .constant) #[IntegerType.mk 32] #[] #[] #[] () insertPoint sorry sorry sorry sorry sorry
  let ctx ← newOp.setAttributes ctx (.fromArray #[("value".toByteArray, sumValue)]) sorry

  let mut ctx ← Rewriter.replaceOp? ctx op newOp sorry sorry sorry sorry sorry

  if (lhsOpResultPtr.getFirstUse ctx sorry).toOption.isNone then
    ctx ← Rewriter.eraseOp ctx lhsOpPtr sorry sorry sorry sorry
  if (rhsOpResultPtr.getFirstUse ctx sorry).toOption.isNone then
    ctx ← Rewriter.eraseOp ctx rhsOpPtr sorry sorry sorry sorry
  return ctx

-- buffed (def_lemma := false)
def addIZeroFoldingSim (ctx : Sim.IRContext OpCode) (op : Sim.OperationPtr) : Option (Sim.IRContext OpCode) := do
  if op.getOpType ctx sorry ≠ .arith .addi then
    return ctx

  -- Get the rhs and check that it is the constant 0
  let rhsValuePtr := op.getOperandPtr ctx 1 sorry
  let rhsValue := rhsValuePtr.getValue ctx sorry
  -- Unsafe...
  let rhsOpResultPtr : Sim.OpResultPtr := ⟨rhsValue.impl, sorry⟩
  let rhsOpPtr := rhsOpResultPtr.getOwner ctx sorry

  if rhsOpPtr.getOpType ctx sorry ≠ .arith .constant then
    return ctx

  -- We store a constant value as an integer attribute "value"
  let rhsAttrs := rhsOpPtr.getAttributes ctx sorry
  let some (attrName, Attribute.integerAttr rhsConstValue) := rhsAttrs.entries[0]? | return ctx
  if rhsConstValue.value ≠ 0 ∨ attrName ≠ "value".toByteArray then
    return ctx

  -- Get the lhs value
  let lhsValuePtr := op.getOperandPtr ctx 0 sorry
  let lhsValue := lhsValuePtr.getValue ctx sorry

  let oldValuePtr := op.getResultPtr ctx 0 sorry
  let oldValue : Sim.ValuePtr := ⟨oldValuePtr.impl, sorry⟩
  let ctx ← Rewriter.replaceValue? ctx oldValue lhsValue sorry sorry

  let ctx ← Rewriter.eraseOp ctx op sorry sorry sorry sorry

  if (rhsOpResultPtr.getFirstUse ctx sorry).toOption.isNone then
    return Rewriter.eraseOp ctx rhsOpPtr sorry sorry sorry sorry

  return ctx

-- buffed (def_lemma := false)
def mulITwoReduceSim (ctx : Sim.IRContext OpCode) (op : Sim.OperationPtr) : Option (Sim.IRContext OpCode) := do
  if op.getOpType ctx sorry ≠ .arith .muli then
    return ctx

  -- Get the rhs and check that it is the constant 2
  let rhsValuePtr := op.getOperandPtr ctx 1 sorry
  let rhsValue := rhsValuePtr.getValue ctx sorry
  -- Unsafe...
  let rhsOpResultPtr : Sim.OpResultPtr := ⟨rhsValue.impl, sorry⟩
  let rhsOpPtr := rhsOpResultPtr.getOwner ctx sorry

  if rhsOpPtr.getOpType ctx sorry ≠ .arith .constant then
    return ctx

  -- We store a constant value as an integer attribute "value"
  let rhsAttrs := rhsOpPtr.getAttributes ctx sorry
  let some (attrName, Attribute.integerAttr rhsConstValue) := rhsAttrs.entries[0]? | return ctx
  if rhsConstValue.value ≠ 2 ∨ attrName ≠ "value".toByteArray then
    return ctx

  -- Get the lhs value
  let lhsValuePtr := op.getOperandPtr ctx 0 sorry
  let lhsValue := lhsValuePtr.getValue ctx sorry

  let insertPoint := InsertPoint.before ⟨op.impl.toNat⟩
  let (ctx, newOp) ← Rewriter.createOp ctx (.arith .addi) #[IntegerType.mk 32] #[lhsValue, lhsValue] #[] #[] () insertPoint sorry sorry sorry sorry sorry
  let ctx ← Rewriter.replaceOp? ctx op newOp sorry sorry sorry sorry sorry

  if (rhsOpResultPtr.getFirstUse ctx sorry).toOption.isNone then
    return Rewriter.eraseOp ctx rhsOpPtr sorry sorry sorry sorry

  return ctx

end Custom

namespace Program

buffed (def_lemma := false)
def emptySim : Option (Sim.IRContext OpCode × Sim.OperationPtr × InsertPoint) := do
  let (ctx, topLevelOp) ← IRContext.create OpCode
  let region := topLevelOp.getRegionPtr! ctx 0
  let block := region.getFirstBlock! ctx
  let insertPoint := InsertPoint.atEnd ⟨block.impl.toNat⟩
  (ctx, topLevelOp, insertPoint)

-- Create a program that looks like:
-- func @main() -> u64 {
--   %0 = arith.constant [root] : u64
--   %1 = arith.constant [inc] : u64
--   %2 = [opcode] %0, %1 : u64
--   %3 = arith.constant [inc] : u64
--   %4 = [opcode] %2, %3 : u64
--   ...
buffed (def_lemma := false)
def constFoldTreeSim (opcode : OpCode) (prop : propertiesOf opcode) (size pc : Nat) (root inc : Int) : Option (Sim.IRContext OpCode × Sim.OperationPtr) := do
  let rootAttr := DictionaryAttr.fromArray #[("value".toByteArray, IntegerAttr.mk root (IntegerType.mk 32))]
  let incAttr := DictionaryAttr.fromArray #[("value".toByteArray, IntegerAttr.mk inc (IntegerType.mk 32))]
  let (gctx, topOp, insertPoint) ← empty
  (gctx, topOp)

  -- let mut (gctx, gacc) ← Rewriter.createOp gctx (.arith .constant) #[IntegerType.mk 32] #[] #[] #[] () insertPoint sorry sorry sorry sorry sorry
  -- gctx ← gacc.setAttributes gctx rootAttr sorry

  -- for i in [0:size] do
  --   let ⟨thisOp, prop⟩ : (op : OpCode) × propertiesOf op := if (i % 100 < pc) then ⟨opcode, prop⟩ else ⟨.arith .andi, ()⟩
  --   let (ctx, acc) := (gctx, gacc)
  --   -- Create rhs const
  --   let (ctx, rhsOp) ← Rewriter.createOp ctx (.arith .constant) #[IntegerType.mk 32] #[] #[] #[] () insertPoint sorry sorry sorry sorry sorry
  --   let ctx ← rhsOp.setAttributes ctx incAttr sorry

  --   let lhsValPtr := acc.getResultPtr ctx 0 sorry
  --   let lhsVal : Sim.ValuePtr := ⟨lhsValPtr.impl, sorry⟩
  --   let rhsValPtr := rhsOp.getResultPtr ctx 0 sorry
  --   let rhsVal : Sim.ValuePtr := ⟨rhsValPtr.impl, sorry⟩

  --   let (ctx, acc) ← Rewriter.createOp ctx thisOp #[IntegerType.mk 32] #[lhsVal, rhsVal] #[] #[] prop insertPoint sorry sorry sorry sorry sorry
  --   (gctx, gacc) := (ctx, acc)

  -- let accResPtr := gacc.getResultPtr gctx 0 sorry
  -- let accRes : Sim.ValuePtr := ⟨accResPtr.impl, sorry⟩
  -- let (ctx, op) ← Rewriter.createOp gctx (.test .test) #[] #[accRes] #[] #[] () insertPoint sorry sorry sorry sorry sorry
  -- (ctx, topOp)

end Program

buffed (def_lemma := false)
def printSim (program : Option (Sim.IRContext OpCode × Sim.OperationPtr)) : IO Unit := do
  if let some (ctx, topOp) := program then
    Printer.printModule ctx topOp

/-
-- TODO: the array is bad... We need our own array type or not use arrays
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
-/

def main : IO Unit := do
  (Program.constFoldTree (.arith .addi) () 1 100 42 1) |> print
  -- let N := 10_000_000
  -- let startTime ← IO.monoNanosNow
  -- if let some result := createManyOps N then
  --   let r := result.1
  --   let endTime ← IO.monoNanosNow
  --   let elapsed := endTime - startTime |>.toFloat
  --   let perOp := elapsed / N.toFloat
  --   let perOpUs := perOp / 1_000
  --   IO.println s!"Created operation with result: {result.1.impl}, took {perOpUs} μs per operation."
  --   IO.println s!"Before replacing: {blockLength result.2 r}"
  --   IO.sleep 100
  --   let startTime ← IO.monoNanosNow
  --   if let some result2 := replaceOps result.2 r then
  --     let endTime ← IO.monoNanosNow
  --     let elapsed := endTime - startTime |>.toFloat
  --     IO.sleep 100
  --     let perOp := elapsed / N.toFloat
  --     let perOpUs := perOp / 1_000
  --     IO.println s!"block : {r.impl}"
  --     IO.println s!"block first: {r.getFirstOp result2 (by sorry) |>.impl}"
  --     IO.println s!"block last: {r.getLastOp result2 (by sorry) |>.impl}"
  --     let ctx := dumpOp (r.getFirstOp result2 (by sorry) |>.toOption.get sorry) result2 "first op after replace"
  --     IO.println s!"Replaced operation with result, took {perOpUs} μs per operation. len {blockLength ctx r}"
  -- else
  --   IO.println "Failed to create operations."

-- def printManyOps (n : Nat) : IO Unit := do
--   if let some (ctx, topOp) := createManyOps n then
--     Printer.printModule ctx topOp

-- #eval! printManyOps 5
