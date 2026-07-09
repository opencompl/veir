import Veir.Prelude
import Veir.IR.Basic
import Veir.Rewriter.Basic
import Veir.GlobalOpInfo
import Veir.Printer

open Veir
open Attribute
set_option maxHeartbeats 100000000
set_option warn.sorry false

namespace Program

structure Xoshiro256PP where
  s0 : UInt64
  s1 : UInt64
  s2 : UInt64
  s3 : UInt64

namespace Xoshiro256PP

@[always_inline]
def rol64 (x : UInt64) (k : UInt64) :=
  (x <<< k) ||| (x >>> (64 - k))

@[always_inline]
def step (self : Xoshiro256PP) : Xoshiro256PP × UInt64:=
  let (s0, s1, s2, s3) := (self.s0, self.s1, self.s2, self.s3)

  let result := rol64 (s0 + s3) 23 + s0
  let t := s1 <<< 17

  let s2 := s2 ^^^ s0
  let s3 := s3 ^^^ s1
  let s1 := s1 ^^^ s2
  let s0 := s0 ^^^ s3

  let s2 := s2 ^^^ t
  let s3 := rol64 s3 45

  ({ s0, s1, s2, s3 }, result)

@[always_inline]
def new (seed : Nat := 42) : Xoshiro256PP :=
  let state := {
    s0 := 0xa88f8a3be644a802,
    s1 := 0x7f9ce0f5c6c0e39e,
    s2 := 0x9fecbfa76b135110,
    s3 := 0x6bcf817f7dd191dc ^^^ seed.toUInt64
  }

  step state |>.fst

@[always_inline]
def randU64 (rng : Xoshiro256PP) : Xoshiro256PP × UInt64 :=
  rng.step

@[always_inline]
def randNat63 (rng : Xoshiro256PP) : Xoshiro256PP × Nat :=
  let (rng, val) := rng.randU64
  (rng, (val &&& 0x7FFF_FFFF_FFFF_FFFF).toNat)

@[always_inline]
def randBool (rng : Xoshiro256PP) (pc : Nat := 50) : Xoshiro256PP × Bool :=
  let (rng, val) := rng.randNat63
  (rng, val % 100 < pc)

@[always_inline]
def randIdx {α : Type} (rng : Xoshiro256PP) (arr : Array α) : Xoshiro256PP × Option α :=
  let (rng, val) := rng.randNat63
  (rng, arr[val % arr.size]?)

end Xoshiro256PP

buffed (def_lemma := false)
def emptySim : Option (Sim.IRContext OpCode × Sim.OperationPtr × InsertPoint) := do
  let (ctx, topLevelOp) ← IRContext.create OpCode
  let region := topLevelOp.getRegionPtr! ctx 0
  let block := region.getFirstBlock! ctx
  let insertPoint := InsertPoint.atEnd ⟨block.impl.toNat⟩
  (ctx, topLevelOp, insertPoint)

buffed (def_lemma := false)
def constFoldTreeGoSim (i : Nat) (ctx : Sim.IRContext OpCode) (insertPoint : InsertPoint) (opcode : OpCode)
    (prop : propertiesOf opcode) (pc : Nat) (inc : Int) (accVal : Sim.ValuePtr) : Option (Sim.IRContext OpCode) := do
  match i with
  | 0 =>
    let (ctx, op) ← Rewriter.createOp ctx (.test .test) #[] #[⟨accVal.impl, default⟩] #[] #[] () insertPoint sorry sorry sorry sorry sorry sorry
    ctx
  | i + 1 =>
    let ⟨thisOp, thisProp⟩ : (op : OpCode) × propertiesOf op := if (i % 100 < pc) then ⟨opcode, prop⟩ else ⟨.arith .andi, ()⟩

    -- Create rhs const
    let incAttr := DictionaryAttr.fromArray #[("value".toByteArray, IntegerAttr.mk inc (IntegerType.mk 32))]
    let (ctx, rhsOp) ← Rewriter.createOp ctx (.arith .constant) #[IntegerType.mk 32] #[] #[] #[] () insertPoint sorry sorry sorry sorry sorry sorry
    let ctx ← rhsOp.setAttributes ctx incAttr sorry

    let rhsValPtr := rhsOp.getResultPtr ctx 0 sorry
    let rhsVal : Sim.ValuePtr := ⟨rhsValPtr.impl, rhsValPtr.spec⟩

    let (ctx, acc) ← Rewriter.createOp ctx thisOp #[IntegerType.mk 32] #[⟨accVal.impl, default⟩, ⟨rhsVal.impl, default⟩] #[] #[] thisProp insertPoint sorry sorry sorry sorry sorry
    let accResult := acc.getResultPtr ctx 0 sorry
    let accVal : Sim.ValuePtr := ⟨accResult.impl, accResult.spec⟩
    constFoldTreeGoSim i ctx insertPoint opcode prop pc inc accVal

-- Create a program that looks like:
-- func @main() -> u64 {
--   %0 = arith.constant [root] : u64
--   %1 = arith.constant [inc] : u64
--   %2 = [opcode] %0, %1 : u64
--   %3 = arith.constant [inc] : u64
--   %4 = [opcode] %2, %3 : u64
--   ...
buffed (def_lemma := false)
def constFoldTreeSim (ctx : Sim.IRContext OpCode) (insertPoint : InsertPoint) (opcode : OpCode)
    (prop : propertiesOf opcode) (size pc : Nat) (root inc : Int) : Option (Sim.IRContext OpCode) := do
  let rootAttr := DictionaryAttr.fromArray #[("value".toByteArray, IntegerAttr.mk root (IntegerType.mk 32))]
  let (ctx, acc) ← Rewriter.createOp ctx (.arith .constant) #[IntegerType.mk 32] #[] #[] #[] () insertPoint sorry sorry sorry sorry sorry
  let ctx ← acc.setAttributes ctx rootAttr sorry

  let accResultPtr := acc.getResultPtr ctx 0 sorry
  let accVal : Sim.ValuePtr := ⟨accResultPtr.impl, accResultPtr.spec⟩

  constFoldTreeGo size ctx insertPoint opcode prop pc inc accVal

buffed (def_lemma := false)
def addZeroTreeSim (ctx : Sim.IRContext OpCode) (ip : InsertPoint) (size pc : Nat) : Option (Sim.IRContext OpCode) :=
  constFoldTree ctx ip (.arith .addi) () size pc 42 0

buffed (def_lemma := false)
def addOneTreeSim (ctx : Sim.IRContext OpCode) (ip : InsertPoint) (size pc : Nat) : Option (Sim.IRContext OpCode) :=
  constFoldTree ctx ip (.arith .addi) () size pc 42 1

buffed (def_lemma := false)
def multwoTreeSim (ctx : Sim.IRContext OpCode) (ip : InsertPoint) (size pc : Nat) : Option (Sim.IRContext OpCode) :=
  constFoldTree ctx ip (.arith .muli) () size pc 42 2

buffed (def_lemma := false)
def constFoldTreeSparseGoSim (ctx : Sim.IRContext OpCode) (rng : Xoshiro256PP) (insertPoint : InsertPoint) (opcode : OpCode)
    (prop : propertiesOf opcode) (size pc : Nat) (inc : Int) (constants runningTotals : Array Buffed.ValueImplMPtr) : Option (Sim.IRContext OpCode) := do
  if runningTotals.size ≥ size then
    let back := runningTotals.back!
    let (ctx, op) ← Rewriter.createOp ctx (.test .test) #[] #[⟨back, default⟩] #[] #[] () insertPoint sorry sorry sorry sorry sorry sorry
    ctx
  else
    let (rng, const) := rng.randBool 20

    if const then
      let incAttr := DictionaryAttr.fromArray #[("value".toByteArray, IntegerAttr.mk inc (IntegerType.mk 32))]
      let (ctx, op) ← Rewriter.createOp ctx (.arith .constant) #[IntegerType.mk 32] #[] #[] #[] () insertPoint sorry sorry sorry sorry sorry sorry
      let ctx ← op.setAttributes ctx incAttr sorry
      let constResultPtr := op.getResultPtr ctx 0 sorry
      let constants := constants.push constResultPtr.impl
      constFoldTreeSparseGoSim ctx rng insertPoint opcode prop size pc inc constants runningTotals

    else
      let (rng, lhs) := rng.randIdx runningTotals
      if let some lhs := lhs then
        let (rng, rhs) := rng.randIdx constants
        if let some rhs := rhs then
          let (rng, b) := rng.randBool pc
          let ⟨thisOp, thisProp⟩ : (op : OpCode) × propertiesOf op := if b then ⟨opcode, prop⟩ else ⟨.arith .andi, ()⟩

          let (ctx, op) ← Rewriter.createOp ctx thisOp #[IntegerType.mk 32] #[⟨lhs, default⟩, ⟨rhs, default⟩] #[] #[] thisProp insertPoint sorry sorry sorry sorry sorry sorry
          let result := op.getResultPtr ctx 0 sorry
          let runningTotals := runningTotals.push result.impl
          constFoldTreeSparseGoSim ctx rng insertPoint opcode prop size pc inc constants runningTotals
        else
          constFoldTreeSparseGoSim ctx rng insertPoint opcode prop size pc inc constants runningTotals
      else
        constFoldTreeSparseGoSim ctx rng insertPoint opcode prop size pc inc constants runningTotals

partial_fixpoint

-- Create a program that looks like constFoldTree but with randomly selected constants as rhs and
-- randomly selected previous ops as lhs
buffed (def_lemma := false)
def constFoldTreeSparseSim (ctx : Sim.IRContext OpCode) (insertPoint : InsertPoint) (opcode : OpCode)
    (prop : propertiesOf opcode) (size pc : Nat) (root inc : Int) : Option (Sim.IRContext OpCode) := do
  let rootAttr := DictionaryAttr.fromArray #[("value".toByteArray, IntegerAttr.mk root (IntegerType.mk 32))]
  let (ctx, root) ← Rewriter.createOp ctx (.arith .constant) #[IntegerType.mk 32] #[] #[] #[] () insertPoint sorry sorry sorry sorry sorry
  let ctx ← root.setAttributes ctx rootAttr sorry
  let  rootResult := root.getResultPtr ctx 0 sorry

  let runningTotals := #[rootResult.impl]
  let constants := #[]
  let rng := .new

  constFoldTreeSparseGo ctx rng insertPoint opcode prop size pc inc constants runningTotals

buffed (def_lemma := false)
def addZeroTreeSparseSim (ctx : Sim.IRContext OpCode) (ip : InsertPoint) (size pc : Nat) : Option (Sim.IRContext OpCode) :=
  constFoldTreeSparse ctx ip (.arith .addi) () size pc 42 0

buffed (def_lemma := false)
def addOneTreeSparseSim (ctx : Sim.IRContext OpCode) (ip : InsertPoint) (size pc : Nat) : Option (Sim.IRContext OpCode) :=
  constFoldTreeSparse ctx ip (.arith .addi) () size pc 42 1

buffed (def_lemma := false)
def multwoTreeSparseSim (ctx : Sim.IRContext OpCode) (ip : InsertPoint) (size pc : Nat) : Option (Sim.IRContext OpCode) :=
  constFoldTreeSparse ctx ip (.arith .muli) () size pc 42 2

end Program

namespace Custom

def _root_.Veir.ValuePtr.asOpResultPtr (ptr : ValuePtr) : OpResultPtr :=
  match ptr with
  | .opResult ptr => ptr
  | _ => default

buffed (def_lemma := false)
def addIConstantFoldingSim (ctx : Sim.IRContext OpCode) (op : Sim.OperationPtr) : Option (Sim.IRContext OpCode) := do
  if op.getOpType ctx sorry ≠ .arith .addi then
    return ctx

  -- Get the lhs and check that it is a constant
  let lhsValuePtr := op.getOperandPtr ctx 0 sorry
  let lhsValue := lhsValuePtr.getValue ctx sorry
  -- Unsafe...
  let lhsOpResultPtr : Sim.OpResultPtr := ⟨lhsValue.impl, lhsValue.spec.asOpResultPtr⟩
  let lhsOpPtr := lhsOpResultPtr.getOwner ctx sorry

  if lhsOpPtr.getOpType ctx sorry ≠ .arith .constant then
    return ctx

  -- Get the rhs and check that it is a constant
  let rhsValuePtr := op.getOperandPtr ctx 1 sorry
  let rhsValue := rhsValuePtr.getValue ctx sorry
  -- Unsafe...
  let rhsOpResultPtr : Sim.OpResultPtr := ⟨rhsValue.impl, rhsValue.spec.asOpResultPtr⟩
  let rhsOpPtr := rhsOpResultPtr.getOwner ctx sorry

  if rhsOpPtr.getOpType ctx sorry ≠ .arith .constant then
    return ctx

  -- Get the lhs value
  let lhsAttrs := lhsOpPtr.getAttributes ctx sorry
  let some (attrName, Attribute.integerAttr lhsConstValue) := lhsAttrs.entries[0]? | return ctx
  if attrName ≠ "value".toByteArray then
    return ctx

  -- Get the rhs value
  let rhsAttrs := rhsOpPtr.getAttributes ctx sorry
  let some (attrName, Attribute.integerAttr rhsConstValue) := rhsAttrs.entries[0]? | return ctx
  if attrName ≠ "value".toByteArray then
    return ctx

  -- Compute the sum
  let sumValue := IntegerAttr.mk (rhsConstValue.value + lhsConstValue.value) (IntegerType.mk 32)
  let insertPoint := InsertPoint.before ⟨op.impl.toNat⟩
  let (ctx, newOp) ← Rewriter.createOp ctx (.arith .constant) #[IntegerType.mk 32] #[] #[] #[] () insertPoint sorry sorry sorry sorry sorry
  let ctx ← newOp.setAttributes ctx (.fromArray #[("value".toByteArray, sumValue)]) sorry

  let ctx ← Rewriter.replaceOp? ctx op newOp sorry sorry sorry sorry sorry

  match (lhsOpResultPtr.getFirstUse ctx sorry).toOption, (rhsOpResultPtr.getFirstUse ctx sorry).toOption with
  | some _, some _ => ctx
  | none, some _ => (Rewriter.eraseOp ctx lhsOpPtr sorry sorry sorry sorry : Option (Sim.IRContext OpCode))
  | some _, none => (Rewriter.eraseOp ctx rhsOpPtr sorry sorry sorry sorry : Option (Sim.IRContext OpCode))
  | none, none =>
    let ctx ← (Rewriter.eraseOp ctx lhsOpPtr sorry sorry sorry sorry : Option (Sim.IRContext OpCode))
    (Rewriter.eraseOp ctx rhsOpPtr sorry sorry sorry sorry : Option (Sim.IRContext OpCode))


buffed (def_lemma := false)
def rewriteForwardsAddIConstFoldingGoSim (ctx : Sim.IRContext OpCode) (maybeOp : Sim.OptionOperationPtr) : Option (Sim.IRContext OpCode) := do
  match maybeOp.toOption with
  | none => ctx
  | some op =>
    let next := op.getNextOp ctx sorry
    let ctx ← addIConstantFolding ctx op
    rewriteForwardsAddIConstFoldingGoSim ctx next
partial_fixpoint

buffed (inline := false) (def_lemma := false)
def rewriteForwardsAddIConstFoldingSim (ctx : Sim.IRContext OpCode) (topOp : Sim.OperationPtr) : Option (Sim.IRContext OpCode) := do
  let region := topOp.getRegionPtr! ctx 0
  let block ← (region.getFirstBlock! ctx).toOption
  let maybeOp := (block.getFirstOp! ctx)
  rewriteForwardsAddIConstFoldingGo ctx maybeOp

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

def print (ctx : Sim.IRContext OpCode) (topOp : Sim.OperationPtr) : IO Unit := do
  Printer.printModule ctx topOp

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
        () (some insertPoint) sorry sorry sorry sorry sorry sorry with
    | some (ctx, op) =>
      createManyOpsLoopSim ctx insertPoint prev1
        (Sim.ValuePtr.fromOpResultPtr (op.getResultPtr ctx 0 sorry)) n
    | _ => none

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

buffed (def_lemma := false)
def blockLength.loopSim (ctx : Sim.IRContext OpCode) (op : Sim.OperationPtr) (count : UInt64 := 0) : UInt64 :=
  -- let ctx := dumpOp op ctx "blockLength.loopSim"
  match op.getNextOp ctx (by sorry) |>.toOption with
  | none => count
  | some nextOp => blockLength.loopSim ctx nextOp (count + 1)
partial_fixpoint

buffed (def_lemma := false)
def blockLengthSim (ctx : Sim.IRContext OpCode) (block : Sim.BlockPtr) : UInt64 := Id.run do
  let first := block.getFirstOp ctx (by sorry) |>.toOption.get sorry
  blockLength.loop ctx first 0

-- set_option trace.Compiler.reduceArity2 true in
def main : IO Unit := do
  let ctx := Program.empty
  IO.println "Created empty"
  match ctx with
  | none => return
  | some (ctx, topOp, ip) =>
    let res := Program.addOneTreeSparse ctx ip 300_000 100
    match res with
    | none => return -- IO.println "err"
    | some ctx =>
      -- IO.println "Constructed"
      let startTime ← IO.monoNanosNow
      if let some ctx := Custom.rewriteForwardsAddIConstFolding ctx topOp then
        let endTime ← IO.monoNanosNow
        IO.println s!"ok: {ctx.buf.size}"
        let time := (endTime - startTime).toFloat / 1_000_000_000
        IO.println s!"time : {time} s"

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
