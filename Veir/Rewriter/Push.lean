module

public import Veir.Rewriter.RewriterPushResult
public import Veir.Rewriter.RewriterPushOperand
public import Veir.Rewriter.RewriterPushBlockOperand
public import Veir.Rewriter.RewriterPushBlockArgument
public import Veir.Rewriter.RewriterPushRegion
import Veir.IR.GetSet
public import Veir.IR.Buffed.InBounds

/-! Rewriter-specific fields for the paired pushes. The slot initializers are used only
in the proofs: the executable path appends through the checked raw accessor. -/
@[expose] public section
namespace Veir.Rewriter
open Veir
variable [HasOpInfo OpInfo] [SerializableOpInfo OpInfo] [HasBuffedOpCode OpInfo]

theorem operandBack_spec (v : Sim.ValuePtr) :
    v.getOpOperandPtrPtr.spec = .valueFirstUse v.spec := by
  simp only [Sim.ValuePtr.getOpOperandPtrPtr, Sim.OpOperandPtrPtr.spec, Erased.map_out]
  unfold Sim.ValuePtr.spec
  cases v.spec'.out <;> rfl

@[inline] def appendResult (op : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo) (type : TypeAttr)
    (ib : op.InBounds ctx) (room : op.spec.getNumResults! ctx.spec < (op.spec.get! ctx.spec).capResults)
    (ha : ctx.buf.attributes.size < UInt64.size) : Sim.RawIRContext OpInfo :=
  op.pushResult ctx type .none ib room ha Sim.OptionOpOperandPtr.none_inBounds

theorem appendResult_sim (op : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo) (type : TypeAttr)
    (ib : op.InBounds ctx) (room : op.spec.getNumResults! ctx.spec < (op.spec.get! ctx.spec).capResults)
    (ha : ctx.buf.attributes.size < UInt64.size) :
    Veir.Sim ⟨(appendResult op ctx type ib room ha).buf, .mk (Rewriter.pushResult ctx.spec op.spec type ib.ib)⟩ := by
  let idx := op.impl.readCountResults! ctx.buf
  have hi : idx.toNat = op.spec.getNumResults! ctx.spec := by
    simpa only [idx, ← ib.sim.out, Sim.IRContext.inner_def, Sim.IRContext.spec, Sim.RawIRContext.spec] using (ctx.countsMatch.results op.spec ib.ib).live
  have hc : idx.toNat < (op.spec.get! ctx.spec).capResults := hi ▸ room
  have payload := Rewriter.resultPayload_matches op ctx idx type ib hi hc (by prove_setLinkBoundsOp ctx op) (by prove_setLinkBoundsResultSlot ctx op idx) ha rfl
  have valid : op.spec.InBounds (Rewriter.pushResult ctx.spec op.spec type ib.ib) := by grind [Rewriter.pushResult]
  apply Sim.Publication.finishOp payload op.spec (by simpa only [Sim.RawIRContext.spec, Erased.out_mk] using valid) Buffed.Operation.Offsets.countResults 8 rfl (by decide) (idx + 1)
  · have hp := ib.sim.out
    simp only [appendResult, Sim.OperationPtr.pushResult, Buffed.OperationMPtr.pushResult,
      Buffed.OperationMPtr.writeCountResults, Rewriter.resultPayload, Buffed.OpResultMPtr.writeKind,
      Buffed.OpResultMPtr.writeType, Buffed.OpResultMPtr.writeFirstUse, Buffed.OpResultMPtr.writeIndex,
      Buffed.OpResultMPtr.writeOwner, Buffed.ValueImplMPtr.writeKind,
      Buffed.OperationMPtr.readCountResults_eq_readCountResults!,
      Buffed.OperationMPtr.getResultPtr_eq_getResultPtr!, Sim.OptionOpOperandPtr.none, idx]
    congr 3 <;> first | exact hp.symm | exact hp | rfl
  · have counts := Sim.OperationPtr.pushResult_countsMatch op ctx (ib := ib) (room := room) (hattrs := ha) (type := type) (firstUse := .none) (fields := Sim.OptionOpOperandPtr.none_inBounds)
    simpa only [Rewriter.pushResult, appendResult, Sim.OperationPtr.pushResult, Sim.OptionOpOperandPtr.spec,
      Sim.OptionOpOperandPtr.none, Erased.out_mk] using counts

@[inline] def appendOperand (op : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo) (v : Sim.ValuePtr)
    (ib : op.InBounds ctx) (room : op.spec.getNumOperands! ctx.spec < (op.spec.get! ctx.spec).capOperands)
    (hv : v.InBounds ctx) : Sim.RawIRContext OpInfo :=
  op.pushOperand ctx v .none v.getOpOperandPtrPtr ib room ⟨hv, Sim.OptionOpOperandPtr.none_inBounds, ⟨Sim.ValuePtr.getOpOperandPtrPtr_sim_of_sim v hv, by rw [operandBack_spec]; exact .valueFirstUseInBounds _ hv.ib⟩⟩

theorem appendOperand_sim (op : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo) (v : Sim.ValuePtr)
    (ib : op.InBounds ctx) (room : op.spec.getNumOperands! ctx.spec < (op.spec.get! ctx.spec).capOperands)
    (hv : v.InBounds ctx) :
    Veir.Sim ⟨(appendOperand op ctx v ib room hv).buf, .mk (Rewriter.pushOperand ctx.spec op.spec v.spec ib.ib hv.ib)⟩ := by
  let idx := op.impl.readCountOperands! ctx.buf
  have hi : idx.toNat = op.spec.getNumOperands! ctx.spec := by
    simpa only [idx, ← ib.sim.out, Sim.IRContext.inner_def, Sim.IRContext.spec, Sim.RawIRContext.spec] using (ctx.countsMatch.operands op.spec ib.ib).live
  have hc : idx.toNat < (op.spec.get! ctx.spec).capOperands := hi ▸ room
  have payload := Rewriter.operandPayload_matches op ctx idx v ib hv hi hc (by prove_setLinkBoundsOp ctx op) rfl (by prove_setLinkBoundsOperandSlot ctx op idx)
  have valid : op.spec.InBounds (Rewriter.pushOperand ctx.spec op.spec v.spec ib.ib hv.ib) := by grind [Rewriter.pushOperand]
  apply Sim.Publication.finishOp payload op.spec (by simpa only [Sim.RawIRContext.spec, Erased.out_mk] using valid) Buffed.Operation.Offsets.countOperands 88 rfl (by decide) (idx + 1)
  · have hp := ib.sim.out
    simp only [appendOperand, Sim.OperationPtr.pushOperand, Buffed.OperationMPtr.pushOperand,
      Buffed.OperationMPtr.writeCountOperands, Rewriter.operandPayload, Buffed.OpOperandMPtr.writeNextUse,
      Buffed.OpOperandMPtr.writeBack, Buffed.OpOperandMPtr.writeOwner, Buffed.OpOperandMPtr.writeValue,
      Buffed.OperationMPtr.readCountOperands_eq_readCountOperands!,
      Buffed.OperationMPtr.computeOperandOffset_eq_computeOperandOffset!, Sim.OptionOpOperandPtr.none,
      Sim.ValuePtr.getOpOperandPtrPtr, idx]
    congr 3 <;> first | exact hp.symm | exact hp | rfl
  · have counts := Sim.OperationPtr.pushOperand_countsMatch op ctx (ib := ib) (room := room) (value := v) (back := v.getOpOperandPtrPtr) (nextUse := .none) (fields := ⟨hv, Sim.OptionOpOperandPtr.none_inBounds, ⟨Sim.ValuePtr.getOpOperandPtrPtr_sim_of_sim v hv, by rw [operandBack_spec]; exact .valueFirstUseInBounds _ hv.ib⟩⟩)
    simpa only [Rewriter.pushOperand, appendOperand, Sim.OperationPtr.pushOperand, operandBack_spec,
      Sim.OpOperandPtrPtr.spec, Sim.OptionOpOperandPtr.spec, Sim.OptionOpOperandPtr.none, Erased.out_mk] using counts

@[inline] def appendBlockOperand (op : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo) (v : Sim.BlockPtr)
    (ib : op.InBounds ctx) (room : op.spec.getNumSuccessors! ctx.spec < (op.spec.get! ctx.spec).capBlockOperands)
    (hv : v.InBounds ctx) : Sim.RawIRContext OpInfo :=
  op.pushBlockOperand ctx v .none v.getBlockOperandPtrPtr ib room ⟨hv, Sim.OptionBlockOperandPtr.none_inBounds, ⟨Sim.BlockPtr.getOpOperandPtrPtr_sim_of_sim v hv, by simpa [Sim.BlockPtr.getBlockOperandPtrPtr, Sim.BlockOperandPtrPtr.spec] using hv.ib⟩⟩

theorem appendBlockOperand_sim (op : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo) (v : Sim.BlockPtr)
    (ib : op.InBounds ctx) (room : op.spec.getNumSuccessors! ctx.spec < (op.spec.get! ctx.spec).capBlockOperands)
    (hv : v.InBounds ctx) :
    Veir.Sim ⟨(appendBlockOperand op ctx v ib room hv).buf, .mk (Rewriter.pushBlockOperand ctx.spec op.spec v.spec ib.ib hv.ib)⟩ := by
  let idx := op.impl.readCountBlockOperands! ctx.buf
  have hi : idx.toNat = op.spec.getNumSuccessors! ctx.spec := by
    simpa only [idx, ← ib.sim.out, Sim.IRContext.inner_def, Sim.IRContext.spec, Sim.RawIRContext.spec] using (ctx.countsMatch.blockOperands op.spec ib.ib).live
  have hc : idx.toNat < (op.spec.get! ctx.spec).capBlockOperands := hi ▸ room
  have payload := Rewriter.blockOperandPayload_matches op ctx idx v ib hv hi hc (by prove_setLinkBoundsOp ctx op) (by prove_setLinkBoundsBlockOperandSlot ctx op idx)
  have valid : op.spec.InBounds (Rewriter.pushBlockOperand ctx.spec op.spec v.spec ib.ib hv.ib) := by grind [Rewriter.pushBlockOperand]
  apply Sim.Publication.finishOp payload op.spec (by simpa only [Sim.RawIRContext.spec, Erased.out_mk] using valid) Buffed.Operation.Offsets.countBlockOperands 56 rfl (by decide) (idx + 1)
  · have hp := ib.sim.out
    simp only [appendBlockOperand, Sim.OperationPtr.pushBlockOperand, Buffed.OperationMPtr.pushBlockOperand,
      Buffed.OperationMPtr.writeCountBlockOperands, Rewriter.blockOperandPayload,
      Buffed.BlockOperandMPtr.writeNextUse, Buffed.BlockOperandMPtr.writeBack, Buffed.BlockOperandMPtr.writeOwner,
      Buffed.BlockOperandMPtr.writeValue, Buffed.OperationMPtr.readCountBlockOperands_eq_readCountBlockOperands!,
      Buffed.OperationMPtr.readNthBlockOperand,
      Buffed.OperationMPtr.computeBlockOperandOffset_eq_computeBlockOperandOffset!,
      Sim.OptionBlockOperandPtr.none, Sim.BlockPtr.getBlockOperandPtrPtr, idx]
    congr 3 <;> first | exact hp.symm | exact hp | rfl
  · have counts := Sim.OperationPtr.pushBlockOperand_countsMatch op ctx (ib := ib) (room := room) (value := v) (back := v.getBlockOperandPtrPtr) (nextUse := .none) (fields := ⟨hv, Sim.OptionBlockOperandPtr.none_inBounds, ⟨Sim.BlockPtr.getOpOperandPtrPtr_sim_of_sim v hv, by simpa [Sim.BlockPtr.getBlockOperandPtrPtr, Sim.BlockOperandPtrPtr.spec] using hv.ib⟩⟩)
    simpa only [Rewriter.pushBlockOperand, appendBlockOperand, Sim.OperationPtr.pushBlockOperand,
      Sim.BlockPtr.getBlockOperandPtrPtr, Sim.BlockOperandPtrPtr.spec, Erased.map_out, Sim.OptionBlockOperandPtr.spec,
      Sim.OptionBlockOperandPtr.none, Erased.out_mk] using counts

@[inline] def appendArgument (bl : Sim.BlockPtr) (ctx : Sim.IRContext OpInfo) (type : TypeAttr)
    (ib : bl.InBounds ctx) (room : bl.spec.getNumArguments! ctx.spec < (bl.spec.get! ctx.spec).capArguments)
    (ha : ctx.buf.attributes.size < UInt64.size) : Sim.RawIRContext OpInfo :=
  bl.pushArgument ctx type .none ib room ha Sim.OptionOpOperandPtr.none_inBounds

theorem appendArgument_sim (bl : Sim.BlockPtr) (ctx : Sim.IRContext OpInfo) (type : TypeAttr)
    (ib : bl.InBounds ctx) (room : bl.spec.getNumArguments! ctx.spec < (bl.spec.get! ctx.spec).capArguments)
    (ha : ctx.buf.attributes.size < UInt64.size) :
    Veir.Sim ⟨(appendArgument bl ctx type ib room ha).buf, .mk (Rewriter.pushBlockArgument ctx.spec bl.spec type ib.ib)⟩ := by
  let idx := bl.impl.readCountArguments! ctx.buf
  have hi : idx.toNat = bl.spec.getNumArguments! ctx.spec := by
    simpa only [idx, ← ib.sim.out, Sim.IRContext.inner_def, Sim.IRContext.spec, Sim.RawIRContext.spec] using (ctx.countsMatch.arguments bl.spec ib.ib).live
  have hc : idx.toNat < (bl.spec.get! ctx.spec).capArguments := hi ▸ room
  have payload := Rewriter.blockArgumentPayload_matches bl ctx idx type ib hi hc (ctx.buf.insertAttrsBounded type ha).1 (ctx.buf.insertAttrsBounded type ha).2 rfl rfl (by simp [Buffed.IRBufContext.insertAttrsBounded]; grind) (by change (bl.impl.getArgumentPtr idx).toNat + Buffed.BlockArgument.size.toNat ≤ ctx.buf.size; prove_setLinkBoundsArgumentSlot ctx bl idx)
  have valid : bl.spec.InBounds (Rewriter.pushBlockArgument ctx.spec bl.spec type ib.ib) := by grind [Rewriter.pushBlockArgument]
  apply Sim.Publication.finishBlock payload bl.spec (by simpa only [Sim.RawIRContext.spec, Erased.out_mk] using valid) Buffed.Block.Offsets.countArguments 56 rfl (by decide) (idx + 1)
  · have hp := ib.sim.out
    simp only [appendArgument, Sim.BlockPtr.pushArgument, Buffed.BlockMPtr.pushArgument,
      Buffed.BlockMPtr.writeCountArguments, Rewriter.blockArgumentPayload, Buffed.BlockArgumentMPtr.writeKind,
      Buffed.BlockArgumentMPtr.writeType, Buffed.BlockArgumentMPtr.writeFirstUse,
      Buffed.BlockArgumentMPtr.writeIndex, Buffed.BlockArgumentMPtr.writeOwner, Buffed.ValueImplMPtr.writeKind,
      Buffed.BlockMPtr.readCountArguments_eq_readCountArguments!, Sim.OptionOpOperandPtr.none, idx]
    congr 3 <;> first | exact hp.symm | exact hp | rfl
  · have counts := Sim.BlockPtr.pushArgument_countsMatch bl ctx (ib := ib) (room := room) (type := type) (firstUse := .none) (hattrs := ha) (fields := Sim.OptionOpOperandPtr.none_inBounds)
    simpa only [Rewriter.pushBlockArgument, appendArgument, Sim.BlockPtr.pushArgument,
      Veir.BlockPtr.getNumArguments!_eq_getNumArguments ib.ib, Sim.OptionOpOperandPtr.spec,
      Sim.OptionOpOperandPtr.none, Erased.out_mk] using counts

@[inline] def linked (op : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo) (rg : Sim.RegionPtr)
    (ib : op.InBounds ctx) (hr : rg.InBounds ctx) : Sim.IRContext OpInfo :=
  Sim.RegionPtr.setParent ctx rg op.toO hr (Sim.OptionOperationPtr.toO_inBounds_of_inBounds op ib)
theorem linked_spec {op : Sim.OperationPtr} {ctx : Sim.IRContext OpInfo} {rg : Sim.RegionPtr} {ib hr} :
    (linked op ctx rg ib hr).spec = rg.spec.setParent ctx.spec (some op.spec) hr.ib := by
  simp [linked, Sim.RegionPtr.setParent_spec, Sim.OperationPtr.toO, Sim.OptionOperationPtr.spec]
theorem linked_op {op : Sim.OperationPtr} {ctx : Sim.IRContext OpInfo} {rg : Sim.RegionPtr} {ib hr} :
    op.InBounds (linked op ctx rg ib hr) := ⟨ib.sim, by rw [linked_spec]; grind⟩
theorem linked_rg {op : Sim.OperationPtr} {ctx : Sim.IRContext OpInfo} {rg : Sim.RegionPtr} {ib hr} :
    rg.InBounds (linked op ctx rg ib hr) := ⟨hr.sim, by rw [linked_spec]; grind⟩
theorem linked_room {op : Sim.OperationPtr} {ctx : Sim.IRContext OpInfo} {rg : Sim.RegionPtr} {ib hr}
    (room : op.spec.getNumRegions! ctx.spec < (op.spec.get! ctx.spec).capRegions) :
    op.spec.getNumRegions! (linked op ctx rg ib hr).spec < (op.spec.get! (linked op ctx rg ib hr).spec).capRegions := by
  rw [linked_spec]; grind

@[inline] def appendRegion (op : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo) (rg : Sim.RegionPtr)
    (ib : op.InBounds ctx) (hr : rg.InBounds ctx) (room : op.spec.getNumRegions! ctx.spec < (op.spec.get! ctx.spec).capRegions) : Sim.RawIRContext OpInfo :=
  op.pushRegion (linked op ctx rg ib hr) rg linked_op (linked_room room) linked_rg

theorem appendRegion_sim (op : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo) (rg : Sim.RegionPtr)
    (ib : op.InBounds ctx) (hr : rg.InBounds ctx) (free : (rg.spec.get! ctx.spec).parent = none)
    (room : op.spec.getNumRegions! ctx.spec < (op.spec.get! ctx.spec).capRegions) :
    Veir.Sim ⟨(appendRegion op ctx rg ib hr room).buf, .mk (Rewriter.pushRegion ctx.spec op.spec rg.spec ib.ib hr.ib free)⟩ := by
  let l := linked op ctx rg ib hr
  have il : op.InBounds l := linked_op
  let idx := op.impl.readCountRegions! l.buf
  have hi : idx.toNat = op.spec.getNumRegions! l.spec := by
    simpa only [idx, ← ib.sim.out, Sim.IRContext.inner_def, Sim.IRContext.spec, Sim.RawIRContext.spec] using (l.countsMatch.regions op.spec il.ib).live
  have hs : l.spec = rg.spec.setParent ctx.spec (some op.spec) hr.ib := linked_spec
  have hi' : idx.toNat = op.spec.getNumRegions! ctx.spec := by rw [hi, hs]; grind
  have hc : idx.toNat < (op.spec.get! ctx.spec).capRegions := hi' ▸ room
  have hdr : op.impl.toNat + Buffed.Operation.sizeBaseNat ≤ ctx.buf.size := by prove_setLinkBoundsOp ctx op
  have hdr' : op.impl.toNat + Buffed.Operation.sizeBaseNat ≤ l.buf.size := by prove_setLinkBoundsOp l op
  have hoff : op.impl.computeRegionsOffset! (OpInfo := OpInfo) l.buf = op.impl.computeRegionsOffset! (OpInfo := OpInfo) ctx.buf := by
    have a := OperationPtr.computeRegionsOffset!_ideal l op il.ib ib.sim hdr'
    have b := OperationPtr.computeRegionsOffset!_ideal ctx op ib.ib ib.sim hdr
    rw [hs] at a; grind [layout_grind]
  have payload := Rewriter.regionPayload_matches op ctx idx rg ib hr free hi' hc (by prove_setLinkBoundsRegion ctx rg) hdr (by prove_setLinkBoundsRegionSlot ctx op idx)
  have valid : op.spec.InBounds (Rewriter.pushRegion ctx.spec op.spec rg.spec ib.ib hr.ib free) := by grind [Rewriter.pushRegion]
  apply Sim.Publication.finishOp payload _ (by simpa only [Sim.RawIRContext.spec, Erased.out_mk] using valid) Buffed.Operation.Offsets.countRegions 72 rfl (by decide) (idx + 1)
  · have hp := ib.sim.out
    simp only [appendRegion, Sim.OperationPtr.pushRegion, Buffed.OperationMPtr.pushRegion, Buffed.OperationMPtr.writeCountRegions,
      Buffed.OperationMPtr.writeNthRegion, Rewriter.regionPayload, Buffed.OperationMPtr.computeRegionOffset,
      Buffed.OperationMPtr.computeRegionsOffset_eq_computeRegionsOffset!, Buffed.OperationMPtr.readCountRegions_eq_readCountRegions!, ← hoff]
    congr 3 <;> first | exact hp.symm | exact hp | rfl
  · have counts := Sim.OperationPtr.pushRegion_countsMatch op l (region := rg) (ib := il) (room := linked_room room) (fields := linked_rg)
    change Sim.CountsMatch ⟨(appendRegion op ctx rg ib hr room).buf, .mk (op.spec.pushRegion l.spec rg.spec il.ib)⟩ at counts
    simpa only [Rewriter.pushRegion, hs, Sim.ValuePtr.getOpOperandPtrPtr, Sim.BlockPtr.getBlockOperandPtrPtr, Sim.OpOperandPtrPtr.spec, Sim.BlockOperandPtrPtr.spec, Sim.OptionOpOperandPtr.spec, Sim.OptionBlockOperandPtr.spec, Sim.OptionOpOperandPtr.none, Sim.OptionBlockOperandPtr.none, Erased.out_mk] using counts

end Veir.Rewriter
