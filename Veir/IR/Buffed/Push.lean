module

public import Veir.IR.Buffed.Basic
import Veir.IR.GetSet
import Veir.IR.Buffed.InBounds
import Veir.IR.Buffed.Frames
import Veir.IR.Buffed.RawAccessorsLemmas

@[expose] public section

namespace Veir
variable [HasOpInfo OpInfo] [SerializableOpInfo OpInfo] [HasBuffedOpCode OpInfo]

@[inline]
def Sim.OperationPtr.pushResult (ptr : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo)
    (type : TypeAttr) (firstUse : Sim.OptionOpOperandPtr)
    (ib : ptr.InBounds ctx)
    (room : ptr.spec.getNumResults! ctx.spec < (ptr.spec.get! ctx.spec).capResults)
    (hattrs : ctx.buf.attributes.size < UInt64.size)
    (_fields : firstUse.InBounds ctx) :
    Sim.RawIRContext OpInfo :=
  let idx := ptr.impl.readCountResults! ctx.buf
  have hi : idx.toNat = ptr.spec.getNumResults! ctx.spec := by
    simpa only [idx, ← ib.sim.out, Sim.IRContext.inner_def, Sim.IRContext.spec, Sim.RawIRContext.spec]
      using (ctx.countsMatch.results ptr.spec ib.ib).live
  have hc := (ctx.sim.encoding_op ptr.spec ib.ib).numResults
  have hr : idx < ptr.impl.readNumResults! ctx.buf := by
    change idx.toNat < (ptr.impl.readNumResults! ctx.buf).toNat
    rw [hi, ← ib.sim.out, ← hc]
    exact room
  let b := (ctx.buf.insertAttrsBounded type hattrs).1
  let tidx := (ctx.buf.insertAttrsBounded type hattrs).2
  let buf := ptr.impl.pushResult b tidx firstUse.impl
    (by change ptr.impl.toNat + Buffed.Operation.sizeBaseNat ≤ ctx.buf.size; prove_setLinkBoundsOp ctx ptr) hr
    (by change (ptr.impl.getResultPtr! ctx.buf idx).toNat + Buffed.OpResult.sizeNat ≤ ctx.buf.size
        prove_setLinkBoundsResultSlot ctx ptr idx)
  ⟨buf, .mk (ptr.spec.pushResult ctx.spec
    { type, firstUse := firstUse.spec, index := ptr.spec.getNumResults! ctx.spec, owner := ptr.spec } ib.ib)⟩

@[inline]
def Sim.OperationPtr.pushOperand (ptr : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo)
    (value : Sim.ValuePtr) (nextUse : Sim.OptionOpOperandPtr) (back : Sim.OpOperandPtrPtr)
    (ib : ptr.InBounds ctx)
    (room : ptr.spec.getNumOperands! ctx.spec < (ptr.spec.get! ctx.spec).capOperands)
    (_fields : value.InBounds ctx ∧ nextUse.InBounds ctx ∧ back.InBounds ctx) :
    Sim.RawIRContext OpInfo :=
  let idx := ptr.impl.readCountOperands! ctx.buf
  have hi : idx.toNat = ptr.spec.getNumOperands! ctx.spec := by
    simpa only [idx, ← ib.sim.out, Sim.IRContext.inner_def, Sim.IRContext.spec, Sim.RawIRContext.spec]
      using (ctx.countsMatch.operands ptr.spec ib.ib).live
  have hc := (ctx.sim.encoding_op ptr.spec ib.ib).numOperands
  have hr : idx < ptr.impl.readNumOperands! ctx.buf := by
    change idx.toNat < (ptr.impl.readNumOperands! ctx.buf).toNat
    rw [hi, ← ib.sim.out, ← hc]
    exact room
  let buf := ptr.impl.pushOperand (OpInfo := OpInfo) ctx.buf value.impl nextUse.impl back.impl
    (by prove_setLinkBoundsOp ctx ptr) hr
    (by prove_setLinkBoundsOperandSlot ctx ptr idx)
  ⟨buf, .mk (ptr.spec.pushOperand ctx.spec
    { value := value.spec, nextUse := nextUse.spec, back := back.spec, owner := ptr.spec } ib.ib)⟩

@[inline]
def Sim.OperationPtr.pushBlockOperand (ptr : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo)
    (value : Sim.BlockPtr) (nextUse : Sim.OptionBlockOperandPtr) (back : Sim.BlockOperandPtrPtr)
    (ib : ptr.InBounds ctx)
    (room : ptr.spec.getNumSuccessors! ctx.spec < (ptr.spec.get! ctx.spec).capBlockOperands)
    (_fields : value.InBounds ctx ∧ nextUse.InBounds ctx ∧ back.InBounds ctx) :
    Sim.RawIRContext OpInfo :=
  let idx := ptr.impl.readCountBlockOperands! ctx.buf
  have hi : idx.toNat = ptr.spec.getNumSuccessors! ctx.spec := by
    simpa only [idx, ← ib.sim.out, Sim.IRContext.inner_def, Sim.IRContext.spec, Sim.RawIRContext.spec]
      using (ctx.countsMatch.blockOperands ptr.spec ib.ib).live
  have hc := (ctx.sim.encoding_op ptr.spec ib.ib).numBlockOperands
  have hr : idx < ptr.impl.readNumBlockOperands! ctx.buf := by
    change idx.toNat < (ptr.impl.readNumBlockOperands! ctx.buf).toNat
    rw [hi, ← ib.sim.out, ← hc]
    exact room
  let buf := ptr.impl.pushBlockOperand (OpInfo := OpInfo) ctx.buf value.impl nextUse.impl back.impl
    (by prove_setLinkBoundsOp ctx ptr) hr
    (by simp only [Buffed.OperationMPtr.readNthBlockOperand!]
        prove_setLinkBoundsBlockOperandSlot ctx ptr idx)
  ⟨buf, .mk (ptr.spec.pushBlockOperand ctx.spec
    { value := value.spec, nextUse := nextUse.spec, back := back.spec, owner := ptr.spec } ib.ib)⟩

@[inline]
def Sim.OperationPtr.pushRegion (ptr : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo)
    (region : Sim.RegionPtr)
    (ib : ptr.InBounds ctx)
    (room : ptr.spec.getNumRegions! ctx.spec < (ptr.spec.get! ctx.spec).capRegions)
    (_fields : region.InBounds ctx) :
    Sim.RawIRContext OpInfo :=
  let idx := ptr.impl.readCountRegions! ctx.buf
  have hi : idx.toNat = ptr.spec.getNumRegions! ctx.spec := by
    simpa only [idx, ← ib.sim.out, Sim.IRContext.inner_def, Sim.IRContext.spec, Sim.RawIRContext.spec]
      using (ctx.countsMatch.regions ptr.spec ib.ib).live
  have hc := (ctx.sim.encoding_op ptr.spec ib.ib).numRegions
  have hr : idx < ptr.impl.readNumRegions! ctx.buf := by
    change idx.toNat < (ptr.impl.readNumRegions! ctx.buf).toNat
    rw [hi, ← ib.sim.out, ← hc]
    exact room
  let buf := ptr.impl.pushRegion (OpInfo := OpInfo) ctx.buf region.impl
    (by prove_setLinkBoundsOp ctx ptr) hr
    (by prove_setLinkBoundsRegionSlot ctx ptr idx)
  ⟨buf, .mk (ptr.spec.pushRegion ctx.spec region.spec ib.ib)⟩

@[inline]
def Sim.BlockPtr.pushArgument (ptr : Sim.BlockPtr) (ctx : Sim.IRContext OpInfo)
    (type : TypeAttr) (firstUse : Sim.OptionOpOperandPtr)
    (ib : ptr.InBounds ctx)
    (room : ptr.spec.getNumArguments! ctx.spec < (ptr.spec.get! ctx.spec).capArguments)
    (hattrs : ctx.buf.attributes.size < UInt64.size)
    (_fields : firstUse.InBounds ctx) :
    Sim.RawIRContext OpInfo :=
  let idx := ptr.impl.readCountArguments! ctx.buf
  have hi : idx.toNat = ptr.spec.getNumArguments! ctx.spec := by
    simpa only [idx, ← ib.sim.out, Sim.IRContext.inner_def, Sim.IRContext.spec, Sim.RawIRContext.spec]
      using (ctx.countsMatch.arguments ptr.spec ib.ib).live
  have hc := (ctx.sim.encoding_block ptr.spec ib.ib).numArguments
  have hr : idx < ptr.impl.readNumArguments! ctx.buf := by
    change idx.toNat < (ptr.impl.readNumArguments! ctx.buf).toNat
    rw [hi, ← ib.sim.out, ← hc]
    exact room
  let b := (ctx.buf.insertAttrsBounded type hattrs).1
  let tidx := (ctx.buf.insertAttrsBounded type hattrs).2
  let buf := ptr.impl.pushArgument b tidx firstUse.impl
    (by change ptr.impl.toNat + Buffed.Block.sizeBaseNat ≤ ctx.buf.size; prove_setLinkBoundsBlock ctx ptr) hr
    (by change (ptr.impl.getArgumentPtr idx).toNat + Buffed.BlockArgument.sizeNat ≤ ctx.buf.size
        prove_setLinkBoundsArgumentSlot ctx ptr idx)
  ⟨buf, .mk (ptr.spec.pushArgument ctx.spec
    { type, firstUse := firstUse.spec, index := ptr.spec.getNumArguments! ctx.spec, owner := ptr.spec, loc := () } ib.ib)⟩

private theorem count_succ {i limit : UInt64} {size capacity : Nat}
    (hi : i.toNat = size) (hc : capacity = limit.toNat) (h : size < capacity) :
    (i + 1).toNat = size + 1 := by
  have := UInt64.toNat_lt_size limit
  rw [UInt64.toNat_add_of_le_size]
  · simp [hi]
  · change i.toNat + 1 < UInt64.size
    omega

theorem Sim.OperationPtr.pushResult_length (ptr : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo)
    {ib room hattrs fields} :
    let ctx' := Sim.OperationPtr.pushResult ptr ctx type firstUse ib room hattrs fields
    (ptr.impl.readCountResults! ctx'.buf).toNat = ptr.spec.getNumResults! ctx'.spec ∧
      ptr.spec.getNumResults! ctx'.spec ≤ (ptr.spec.get! ctx'.spec).capResults := by
  have hi := (ctx.countsMatch.results ptr.spec ib.ib).live
  have hc := (ctx.sim.encoding_op ptr.spec ib.ib).numResults
  simp only [Sim.IRContext.inner_def, Sim.RawIRContext.spec, ib.sim.out] at hi
  rw [ib.sim.out] at hc
  have hs := count_succ hi hc room
  simp only [Sim.OperationPtr.pushResult, Sim.RawIRContext.spec, Erased.out_mk,
    Veir.OperationPtr.getNumResults!_OperationPtr_pushResult, Veir.OperationPtr.capResults!_OperationPtr_pushResult,
    Buffed.OperationMPtr.pushResult, Buffed.OperationMPtr.writeCountResults,
    Buffed.OperationMPtr.readCountResults_eq_readCountResults!, Buffed.OperationMPtr.readCountResults!,
    ExArray.read64!_blit64_self, Buffed.IRBufContext.insertAttrsBounded]
  exact ⟨hs, room⟩

theorem Sim.OperationPtr.pushOperand_length (ptr : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo)
    {ib room fields} :
    let ctx' := Sim.OperationPtr.pushOperand ptr ctx value nextUse back ib room fields
    (ptr.impl.readCountOperands! ctx'.buf).toNat = ptr.spec.getNumOperands! ctx'.spec ∧
      ptr.spec.getNumOperands! ctx'.spec ≤ (ptr.spec.get! ctx'.spec).capOperands := by
  have hi := (ctx.countsMatch.operands ptr.spec ib.ib).live
  have hc := (ctx.sim.encoding_op ptr.spec ib.ib).numOperands
  simp only [Sim.IRContext.inner_def, Sim.RawIRContext.spec, ib.sim.out] at hi
  rw [ib.sim.out] at hc
  have hs := count_succ hi hc room
  simp only [Sim.OperationPtr.pushOperand, Sim.RawIRContext.spec, Erased.out_mk,
    Veir.OperationPtr.getNumOperands!_OperationPtr_pushOperand, Veir.OperationPtr.capOperands!_OperationPtr_pushOperand,
    Buffed.OperationMPtr.pushOperand, Buffed.OperationMPtr.writeCountOperands,
    Buffed.OperationMPtr.readCountOperands_eq_readCountOperands!, Buffed.OperationMPtr.readCountOperands!,
    ExArray.read64!_blit64_self]
  exact ⟨hs, room⟩

theorem Sim.OperationPtr.pushBlockOperand_length (ptr : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo)
    {ib room fields} :
    let ctx' := Sim.OperationPtr.pushBlockOperand ptr ctx value nextUse back ib room fields
    (ptr.impl.readCountBlockOperands! ctx'.buf).toNat = ptr.spec.getNumSuccessors! ctx'.spec ∧
      ptr.spec.getNumSuccessors! ctx'.spec ≤ (ptr.spec.get! ctx'.spec).capBlockOperands := by
  have hi := (ctx.countsMatch.blockOperands ptr.spec ib.ib).live
  have hc := (ctx.sim.encoding_op ptr.spec ib.ib).numBlockOperands
  simp only [Sim.IRContext.inner_def, Sim.RawIRContext.spec, ib.sim.out] at hi
  rw [ib.sim.out] at hc
  have hs := count_succ hi hc room
  simp only [Sim.OperationPtr.pushBlockOperand, Sim.RawIRContext.spec, Erased.out_mk,
    Veir.OperationPtr.getNumSuccessors!_OperationPtr_pushBlockOperand, Veir.OperationPtr.capBlockOperands!_OperationPtr_pushBlockOperand,
    Buffed.OperationMPtr.pushBlockOperand, Buffed.OperationMPtr.writeCountBlockOperands,
    Buffed.OperationMPtr.readCountBlockOperands_eq_readCountBlockOperands!, Buffed.OperationMPtr.readCountBlockOperands!,
    ExArray.read64!_blit64_self]
  exact ⟨hs, room⟩

theorem Sim.OperationPtr.pushRegion_length (ptr : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo)
    {ib room fields} :
    let ctx' := Sim.OperationPtr.pushRegion ptr ctx region ib room fields
    (ptr.impl.readCountRegions! ctx'.buf).toNat = ptr.spec.getNumRegions! ctx'.spec ∧
      ptr.spec.getNumRegions! ctx'.spec ≤ (ptr.spec.get! ctx'.spec).capRegions := by
  have hi := (ctx.countsMatch.regions ptr.spec ib.ib).live
  have hc := (ctx.sim.encoding_op ptr.spec ib.ib).numRegions
  simp only [Sim.IRContext.inner_def, Sim.RawIRContext.spec, ib.sim.out] at hi
  rw [ib.sim.out] at hc
  have hs := count_succ hi hc room
  simp only [Sim.OperationPtr.pushRegion, Sim.RawIRContext.spec, Erased.out_mk,
    Veir.OperationPtr.getNumRegions!_OperationPtr_pushRegion, Veir.OperationPtr.capRegions!_OperationPtr_pushRegion,
    Buffed.OperationMPtr.pushRegion, Buffed.OperationMPtr.writeCountRegions,
    Buffed.OperationMPtr.readCountRegions_eq_readCountRegions!, Buffed.OperationMPtr.readCountRegions!,
    ExArray.read64!_blit64_self]
  exact ⟨hs, room⟩

theorem Sim.BlockPtr.pushArgument_length (ptr : Sim.BlockPtr) (ctx : Sim.IRContext OpInfo)
    {ib room hattrs fields} :
    let ctx' := Sim.BlockPtr.pushArgument ptr ctx type firstUse ib room hattrs fields
    (ptr.impl.readCountArguments! ctx'.buf).toNat = ptr.spec.getNumArguments! ctx'.spec ∧
      ptr.spec.getNumArguments! ctx'.spec ≤ (ptr.spec.get! ctx'.spec).capArguments := by
  have hi := (ctx.countsMatch.arguments ptr.spec ib.ib).live
  have hc := (ctx.sim.encoding_block ptr.spec ib.ib).numArguments
  simp only [Sim.IRContext.inner_def, Sim.RawIRContext.spec, ib.sim.out] at hi
  rw [ib.sim.out] at hc
  have hs := count_succ hi hc room
  simp only [Sim.BlockPtr.pushArgument, Sim.RawIRContext.spec, Erased.out_mk,
    Veir.BlockPtr.getNumArguments!_BlockPtr_pushArgument, Veir.BlockPtr.capArguments!_BlockPtr_pushArgument,
    Buffed.BlockMPtr.pushArgument, Buffed.BlockMPtr.writeCountArguments,
    Buffed.BlockMPtr.readCountArguments_eq_readCountArguments!, Buffed.BlockMPtr.readCountArguments!,
    ExArray.read64!_blit64_self, Buffed.IRBufContext.insertAttrsBounded]
  exact ⟨hs, room⟩

end Veir
