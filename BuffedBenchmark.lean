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
    let (ctx, op) ← Rewriter.createOp ctx (.test .test) #[] ⟨#[accVal.impl], #[default], by grind, by grind⟩ ⟨#[], #[], by grind, by grind⟩ ⟨#[], #[], by grind, by grind⟩ () insertPoint sorry sorry sorry sorry sorry sorry
    ctx
  | i + 1 =>
    let ⟨thisOp, thisProp⟩ : (op : OpCode) × propertiesOf op := if (i % 100 < pc) then ⟨opcode, prop⟩ else ⟨.arith .andi, ()⟩

    -- Create rhs const
    let incAttr := DictionaryAttr.fromArray #[("value".toByteArray, IntegerAttr.mk inc (IntegerType.mk 32))]
    let (ctx, rhsOp) ← Rewriter.createOp ctx (.arith .constant) #[IntegerType.mk 32] ⟨#[], #[], by grind, by grind⟩ ⟨#[], #[], by grind, by grind⟩ ⟨#[], #[], by grind, by grind⟩ () insertPoint sorry sorry sorry sorry sorry sorry
    let ctx ← rhsOp.setAttributes ctx incAttr sorry

    let rhsValPtr := rhsOp.getResultPtr ctx 0 sorry
    let rhsVal : Sim.ValuePtr := ⟨rhsValPtr.impl, rhsValPtr.spec⟩

    let (ctx, acc) ← Rewriter.createOp ctx thisOp #[IntegerType.mk 32] ⟨#[accVal.impl, rhsVal.impl], #[default, default], by grind, by grind⟩ ⟨#[], #[], by grind, by grind⟩ ⟨#[], #[], by grind, by grind⟩ thisProp insertPoint sorry sorry sorry sorry sorry
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
  let (ctx, acc) ← Rewriter.createOp ctx (.arith .constant) #[IntegerType.mk 32] ⟨#[], #[], by grind, by grind⟩ ⟨#[], #[], by grind, by grind⟩ ⟨#[], #[], by grind, by grind⟩ () insertPoint sorry sorry sorry sorry sorry
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
def mulTwoTreeSim (ctx : Sim.IRContext OpCode) (ip : InsertPoint) (size pc : Nat) : Option (Sim.IRContext OpCode) :=
  constFoldTree ctx ip (.arith .muli) () size pc 42 2

buffed (def_lemma := false)
def constFoldTreeSparseGoSim (ctx : Sim.IRContext OpCode) (rng : Xoshiro256PP) (insertPoint : InsertPoint) (opcode : OpCode)
    (prop : propertiesOf opcode) (size pc : Nat) (inc : Int) (constants runningTotals : Array Buffed.ValueImplMPtr) : Option (Sim.IRContext OpCode) := do
  if runningTotals.size ≥ size then
    let back := runningTotals.back!
    let (ctx, op) ← Rewriter.createOp ctx (.test .test) #[] ⟨#[back], #[default], by grind, by grind⟩ ⟨#[], #[], by grind, by grind⟩ ⟨#[], #[], by grind, by grind⟩ () insertPoint sorry sorry sorry sorry sorry sorry
    ctx
  else
    let (rng, const) := rng.randBool 20

    if const then
      let incAttr := DictionaryAttr.fromArray #[("value".toByteArray, IntegerAttr.mk inc (IntegerType.mk 32))]
      let (ctx, op) ← Rewriter.createOp ctx (.arith .constant) #[IntegerType.mk 32] ⟨#[], #[], by grind, by grind⟩ ⟨#[], #[], by grind, by grind⟩ ⟨#[], #[], by grind, by grind⟩ () insertPoint sorry sorry sorry sorry sorry sorry
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

          let (ctx, op) ← Rewriter.createOp ctx thisOp #[IntegerType.mk 32] ⟨#[lhs, rhs], #[default, default], by grind, by grind⟩ ⟨#[], #[], by grind, by grind⟩ ⟨#[], #[], by grind, by grind⟩ thisProp insertPoint sorry sorry sorry sorry sorry sorry
          let result := op.getResultPtr ctx 0 sorry
          let runningTotals := runningTotals.push result.impl
          constFoldTreeSparseGoSim ctx rng insertPoint opcode prop size pc inc constants runningTotals
        else
          constFoldTreeSparseGoSim ctx rng insertPoint opcode prop size pc inc constants runningTotals
      else
        constFoldTreeSparseGoSim ctx rng insertPoint opcode prop size pc inc constants runningTotals
partial_fixpoint

buffed (def_lemma := false)
def constReuseTreeGoSim (i : Nat) (ctx : Sim.IRContext OpCode) (insertPoint : InsertPoint) (opcode : OpCode)
    (prop : propertiesOf opcode) (pc : Nat) (accVal reuseVal : Sim.ValuePtr) : Option (Sim.IRContext OpCode) := do
  match i with
  | 0 =>
    let (ctx, op) ← Rewriter.createOp ctx (.test .test) #[] ⟨#[accVal.impl], #[default], by grind, by grind⟩ ⟨#[], #[], by grind, by grind⟩ ⟨#[], #[], by grind, by grind⟩ () insertPoint sorry sorry sorry sorry sorry sorry
    ctx
  | i + 1 =>
    let ⟨thisOp, thisProp⟩ : (op : OpCode) × propertiesOf op := if (i % 100 < pc) then ⟨opcode, prop⟩ else ⟨.arith .andi, ()⟩

    let (ctx, acc) ← Rewriter.createOp ctx thisOp #[IntegerType.mk 32] ⟨#[accVal.impl, reuseVal.impl], #[default, default], by grind, by grind⟩ ⟨#[], #[], by grind, by grind⟩ ⟨#[], #[], by grind, by grind⟩ thisProp insertPoint sorry sorry sorry sorry sorry sorry
    let accResult := acc.getResultPtr ctx 0 sorry
    let accVal : Sim.ValuePtr := ⟨accResult.impl, accResult.spec⟩
    constReuseTreeGoSim i ctx insertPoint opcode prop pc accVal reuseVal

-- Create a program that looks like:
-- func @main() -> u64 {
--   %0 = arith.constant [root] : u64
--   %reuse = arith.constant [inc]: u64
--   %2 = [opcode] %0, %reuse : u64
--   %3 = [opcode] %2, %reuse : u64
--   ...
buffed (def_lemma := false)
def constReuseTreeSim (ctx : Sim.IRContext OpCode) (insertPoint : InsertPoint) (opcode : OpCode)
    (prop : propertiesOf opcode) (size pc : Nat) (root inc : Int) : Option (Sim.IRContext OpCode) := do
  let rootAttr := DictionaryAttr.fromArray #[("value".toByteArray, IntegerAttr.mk root (IntegerType.mk 32))]
  let incAttr := DictionaryAttr.fromArray #[("value".toByteArray, IntegerAttr.mk inc (IntegerType.mk 32))]

  let (ctx, acc) ← Rewriter.createOp ctx (.arith .constant) #[IntegerType.mk 32] ⟨#[], #[], by grind, by grind⟩ ⟨#[], #[], by grind, by grind⟩ ⟨#[], #[], by grind, by grind⟩ () insertPoint sorry sorry sorry sorry sorry
  let ctx ← acc.setAttributes ctx rootAttr sorry

  let (ctx, reuse) ← Rewriter.createOp ctx (.arith .constant) #[IntegerType.mk 32] ⟨#[], #[], by grind, by grind⟩ ⟨#[], #[], by grind, by grind⟩ ⟨#[], #[], by grind, by grind⟩ () insertPoint sorry sorry sorry sorry sorry
  let ctx ← reuse.setAttributes ctx incAttr sorry

  let accResult := acc.getResultPtr ctx 0 sorry
  let accVal : Sim.ValuePtr := ⟨accResult.impl, accResult.spec⟩

  let reuseResult := reuse.getResultPtr ctx 0 sorry
  let reuseVal : Sim.ValuePtr := ⟨reuseResult.impl, reuseResult.spec⟩

  constReuseTreeGo size ctx insertPoint opcode prop pc accVal reuseVal

buffed (inline := false) (def_lemma := false)
def addZeroReuseTreeSim (ctx : Sim.IRContext OpCode) (ip : InsertPoint) (size pc : Nat) : Option (Sim.IRContext OpCode) :=
  constReuseTree ctx ip (.arith .addi) () size pc 42 0

-- Create a program that looks like:
-- func @main() -> u64 {
--   %0 = arith.constant [lhs] : u64
--   %1 = arith.constant [rhs] : u64
--   %reuse = [opcode] %0, %1 : u64
--   %3 = [opcode] %reuse, %reuse : u64
--   %4 = [opcode] %3, %reuse : u64
--   %5 = [opcode] %4, %reuse : u64
--   ...
buffed (def_lemma := false)
def constLotsOfReuseTreeSim (ctx : Sim.IRContext OpCode) (insertPoint : InsertPoint) (opcode : OpCode)
    (prop : propertiesOf opcode) (size pc : Nat) (lhs rhs : Int) : Option (Sim.IRContext OpCode) := do
  let lhsAttr := DictionaryAttr.fromArray #[("value".toByteArray, IntegerAttr.mk lhs (IntegerType.mk 32))]
  let rhsAttr := DictionaryAttr.fromArray #[("value".toByteArray, IntegerAttr.mk rhs (IntegerType.mk 32))]

  let (ctx, lhsOp) ← Rewriter.createOp ctx (.arith .constant) #[IntegerType.mk 32] ⟨#[], #[], by grind, by grind⟩ ⟨#[], #[], by grind, by grind⟩ ⟨#[], #[], by grind, by grind⟩ () insertPoint sorry sorry sorry sorry sorry
  let ctx ← lhsOp.setAttributes ctx lhsAttr sorry

  let (ctx, rhsOp) ← Rewriter.createOp ctx (.arith .constant) #[IntegerType.mk 32] ⟨#[], #[], by grind, by grind⟩ ⟨#[], #[], by grind, by grind⟩ ⟨#[], #[], by grind, by grind⟩ () insertPoint sorry sorry sorry sorry sorry
  let ctx ← rhsOp.setAttributes ctx rhsAttr sorry

  let lhsResult := lhsOp.getResultPtr ctx 0 sorry
  let lhsVal : Sim.ValuePtr := ⟨lhsResult.impl, lhsResult.spec⟩

  let rhsResult := rhsOp.getResultPtr ctx 0 sorry
  let rhsVal : Sim.ValuePtr := ⟨rhsResult.impl, rhsResult.spec⟩

  let (ctx, reuse) ← Rewriter.createOp ctx opcode #[IntegerType.mk 32] ⟨#[lhsVal.impl, rhsVal.impl], #[default, default], by grind, by grind⟩ ⟨#[], #[], by grind, by grind⟩ ⟨#[], #[], by grind, by grind⟩ prop insertPoint sorry sorry sorry sorry sorry sorry
  let reuseResult := reuse.getResultPtr ctx 0 sorry
  let reuseVal : Sim.ValuePtr := ⟨reuseResult.impl, reuseResult.spec⟩

  constReuseTreeGo size ctx insertPoint opcode prop pc reuseVal reuseVal

buffed (inline := false) (def_lemma := false)
def addZeroLotsOfReuseTreeSim (ctx : Sim.IRContext OpCode) (ip : InsertPoint) (size pc : Nat) : Option (Sim.IRContext OpCode) :=
  constLotsOfReuseTree ctx ip (.arith .addi) () size pc 42 0

-- Create a program that looks like constFoldTree but with randomly selected constants as rhs and
-- randomly selected previous ops as lhs
buffed (def_lemma := false)
def constFoldTreeSparseSim (ctx : Sim.IRContext OpCode) (insertPoint : InsertPoint) (opcode : OpCode)
    (prop : propertiesOf opcode) (size pc : Nat) (root inc : Int) : Option (Sim.IRContext OpCode) := do
  let rootAttr := DictionaryAttr.fromArray #[("value".toByteArray, IntegerAttr.mk root (IntegerType.mk 32))]
  let (ctx, root) ← Rewriter.createOp ctx (.arith .constant) #[IntegerType.mk 32] ⟨#[], #[], by grind, by grind⟩ ⟨#[], #[], by grind, by grind⟩ ⟨#[], #[], by grind, by grind⟩ () insertPoint sorry sorry sorry sorry sorry
  let ctx ← root.setAttributes ctx rootAttr sorry
  let  rootResult := root.getResultPtr ctx 0 sorry

  let runningTotals := #[rootResult.impl]
  let constants := #[]
  let rng := .new

  constFoldTreeSparseGo ctx rng insertPoint opcode prop size pc inc constants runningTotals

buffed (inline := false) (def_lemma := false)
def addZeroTreeSparseSim (ctx : Sim.IRContext OpCode) (ip : InsertPoint) (size pc : Nat) : Option (Sim.IRContext OpCode) :=
  constFoldTreeSparse ctx ip (.arith .addi) () size pc 42 0

buffed (inline := false) (def_lemma := false)
def addOneTreeSparseSim (ctx : Sim.IRContext OpCode) (ip : InsertPoint) (size pc : Nat) : Option (Sim.IRContext OpCode) :=
  constFoldTreeSparse ctx ip (.arith .addi) () size pc 42 1

buffed (inline := false) (def_lemma := false)
def mulTwoTreeSparseSim (ctx : Sim.IRContext OpCode) (ip : InsertPoint) (size pc : Nat) : Option (Sim.IRContext OpCode) :=
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
  let (ctx, newOp) ← Rewriter.createOp ctx (.arith .constant) #[IntegerType.mk 32] ⟨#[], #[], by grind, by grind⟩ ⟨#[], #[], by grind, by grind⟩ ⟨#[], #[], by grind, by grind⟩ () insertPoint sorry sorry sorry sorry sorry
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

buffed (def_lemma := false)
def rewriteForwardsAddIConstFoldingSim (ctx : Sim.IRContext OpCode) (topOp : Sim.OperationPtr) : Option (Sim.IRContext OpCode) := do
  let region := topOp.getRegionPtr! ctx 0
  let block ← (region.getFirstBlock! ctx).toOption
  let maybeOp := (block.getFirstOp! ctx)
  rewriteForwardsAddIConstFoldingGo ctx maybeOp

buffed (def_lemma := false)
def addIZeroFoldingSim (ctx : Sim.IRContext OpCode) (op : Sim.OperationPtr) : Option (Sim.IRContext OpCode) := do
  if op.getOpType ctx sorry ≠ .arith .addi then
    return ctx

  -- Get the rhs and check that it is the constant 0
  let rhsValuePtr := op.getOperandPtr ctx 1 sorry
  let rhsValue := rhsValuePtr.getValue ctx sorry
  -- Unsafe...
  let rhsOpResultPtr : Sim.OpResultPtr := ⟨rhsValue.impl, rhsValue.spec.asOpResultPtr⟩
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
  let oldValue : Sim.ValuePtr := ⟨oldValuePtr.impl, default⟩
  let ctx ← Rewriter.replaceValue? ctx oldValue lhsValue sorry sorry

  let ctx ← Rewriter.eraseOp ctx op sorry sorry sorry sorry

  if (rhsOpResultPtr.getFirstUse ctx sorry).toOption.isNone then
    return Rewriter.eraseOp ctx rhsOpPtr sorry sorry sorry sorry

  return ctx

buffed (def_lemma := false)
def rewriteForwardsAddIZeroFoldingGoSim (ctx : Sim.IRContext OpCode) (maybeOp : Sim.OptionOperationPtr) : Option (Sim.IRContext OpCode) := do
  match maybeOp.toOption with
  | none => ctx
  | some op =>
    let next := op.getNextOp ctx sorry
    let ctx ← addIZeroFolding ctx op
    rewriteForwardsAddIZeroFoldingGoSim ctx next
partial_fixpoint

buffed (def_lemma := false)
def rewriteForwardsAddIZeroFoldingSim (ctx : Sim.IRContext OpCode) (topOp : Sim.OperationPtr) : Option (Sim.IRContext OpCode) := do
  let region := topOp.getRegionPtr! ctx 0
  let block ← (region.getFirstBlock! ctx).toOption
  let maybeOp := (block.getFirstOp! ctx)
  rewriteForwardsAddIZeroFoldingGo ctx maybeOp

buffed (def_lemma := false)
def rewriteFirstAddIZeroFoldingGoSim (ctx : Sim.IRContext OpCode) (maybeOp : Sim.OptionOperationPtr) : Option (Sim.IRContext OpCode) := do
  match maybeOp.toOption with
  | none => ctx
  | some op =>
    if op.getOpType ctx sorry = .arith .addi then
      let ctx ← addIZeroFolding ctx op
      ctx
    else
      rewriteFirstAddIZeroFoldingGoSim ctx (op.getNextOp ctx sorry)
partial_fixpoint

buffed (def_lemma := false)
def rewriteFirstAddIZeroFoldingSim (ctx : Sim.IRContext OpCode) (topOp : Sim.OperationPtr) : Option (Sim.IRContext OpCode) := do
  let region := topOp.getRegionPtr ctx 0 sorry sorry
  let block ← (region.getFirstBlock ctx sorry).toOption
  let maybeOp := (block.getFirstOp ctx sorry)
  rewriteFirstAddIZeroFoldingGo ctx maybeOp

buffed (def_lemma := false)
def mulITwoReduceSim (ctx : Sim.IRContext OpCode) (op : Sim.OperationPtr) : Option (Sim.IRContext OpCode) := do
  if op.getOpType ctx sorry ≠ .arith .muli then
    return ctx

  -- Get the rhs and check that it is the constant 2
  let rhsValuePtr := op.getOperandPtr ctx 1 sorry
  let rhsValue := rhsValuePtr.getValue ctx sorry
  -- Unsafe...
  let rhsOpResultPtr : Sim.OpResultPtr := ⟨rhsValue.impl, rhsValue.spec.asOpResultPtr⟩
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
  let (ctx, newOp) ← Rewriter.createOp ctx (.arith .addi) #[IntegerType.mk 32] ⟨#[lhsValue.impl, lhsValue.impl], #[default, default], by grind, by grind⟩ ⟨#[], #[], by grind, by grind⟩ ⟨#[], #[], by grind, by grind⟩ () insertPoint sorry sorry sorry sorry sorry
  let ctx ← Rewriter.replaceOp? ctx op newOp sorry sorry sorry sorry sorry

  if (rhsOpResultPtr.getFirstUse ctx sorry).toOption.isNone then
    return Rewriter.eraseOp ctx rhsOpPtr sorry sorry sorry sorry

  return ctx

buffed (def_lemma := false)
def rewriteForwardsMulITwoReduceGoSim (ctx : Sim.IRContext OpCode) (maybeOp : Sim.OptionOperationPtr) : Option (Sim.IRContext OpCode) := do
  match maybeOp.toOption with
  | none => ctx
  | some op =>
    let next := op.getNextOp ctx sorry
    let ctx ← mulITwoReduce ctx op
    rewriteForwardsMulITwoReduceGoSim ctx next
partial_fixpoint

buffed (def_lemma := false)
def rewriteForwardsMulITwoReduceSim (ctx : Sim.IRContext OpCode) (topOp : Sim.OperationPtr) : Option (Sim.IRContext OpCode) := do
  let region := topOp.getRegionPtr! ctx 0
  let block ← (region.getFirstBlock! ctx).toOption
  let maybeOp := (block.getFirstOp! ctx)
  rewriteForwardsMulITwoReduceGo ctx maybeOp

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
    let prev2 : Sim.ValuePtr := ⟨prev2.impl, .blockArgument ⟨⟨0⟩, 0⟩⟩
    let prev1 : Sim.ValuePtr := ⟨prev1.impl, .blockArgument ⟨⟨0⟩, 0⟩⟩
    match Rewriter.createOp ctx (.arith .addi) #[IntegerType.mk 32] ⟨#[prev2.impl, prev1.impl], #[prev2.spec, prev1.spec], by grind, by grind⟩ ⟨#[], #[], by grind, by grind⟩ ⟨#[], #[], by grind, by grind⟩
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

  let some (ctx, op) := Rewriter.createOp ctx (.test .test) #[IntegerType.mk 32] ⟨#[], #[], by grind, by grind⟩ ⟨#[], #[], by grind, by grind⟩ ⟨#[], #[], by grind, by grind⟩
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

@[always_inline]
def ignoreSpec (ctx : Option (Sim.IRContext OpCode)) : Option (Sim.IRContext OpCode) := do
  let ctx ← ctx
  return ⟨ctx.buf, default, sorry⟩

@[always_inline]
def time {α : Type} (name: String) (f: Unit → IO α) : IO α := do
  let startTime ← IO.monoNanosNow
  let res ← f ()
  let endTime ← IO.monoNanosNow
  let elapsedTime := endTime - startTime
  IO.println s!"{name} time (s): {elapsedTime.toFloat / 1000000000}"
  return res

@[always_inline]
def run (size pc : Nat)
    (create : Sim.IRContext OpCode → InsertPoint → Nat → Nat → Option (Sim.IRContext OpCode))
    (rewrite : Sim.IRContext OpCode → Sim.OperationPtr → Option (Sim.IRContext OpCode)) :
    OptionT IO Unit := do
  let some (ctx, topOp, ip) := Program.empty | return
  let ctx ← time "create" (fun () => return ignoreSpec (create ctx ip size pc))
  let ctx ← time "rewrite" (fun () => return ignoreSpec (rewrite ctx topOp))
  let _ctx := ctx

def runBenchmark (benchmark : String) (n pc : Nat) : OptionT IO Unit :=
  open Program in
  open Custom in

  match benchmark with
  | "add-fold-forwards" =>            run n pc addOneTree             rewriteForwardsAddIConstFolding
  | "add-zero-forwards" =>            run n pc addZeroTree            rewriteForwardsAddIZeroFolding
  | "add-zero-reuse-forwards" =>      run n pc addZeroReuseTree       rewriteForwardsAddIZeroFolding
  | "mul-two-forwards" =>             run n pc mulTwoTree             rewriteForwardsMulITwoReduce

  | "add-fold-forwards-sparse" =>     run n pc addOneTreeSparse       rewriteForwardsAddIConstFolding
  | "add-zero-forwards-sparse" =>     run n pc addZeroTreeSparse      rewriteForwardsAddIZeroFolding
  | "mul-two-forwards-sparse" =>      run n pc mulTwoTreeSparse       rewriteForwardsMulITwoReduce

  | "add-zero-reuse-first" =>         run n pc addZeroReuseTree       rewriteFirstAddIZeroFolding
  | "add-zero-lots-of-reuse-first" => run n pc addZeroLotsOfReuseTree rewriteFirstAddIZeroFolding

  | _ => panic! "Unsupported benchmark"

def count := 50_000

def getCountFrom (c : Option String) :=
  match c with
  | none => count
  | some s =>
    match s.toNat? with
    | none => count
    | some n => n

def getPCFrom (c : Option String) :=
  match c with
  | none => 100
  | some s =>
    match s.toNat? with
    | none => 100
    | some n => n

def main (args : List String) : IO Unit := do
  IO.println s!"Benchmark ({args})"
  let count := getCountFrom args[1]?
  if let some bench := args[0]? then
    let _ ← runBenchmark bench count (getPCFrom args[2]?)
  else
    IO.eprintln "Please provide a benchmark name"
    IO.Process.exit 2

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
