module

import all Veir.Rewriter.WfRewriter.Basic
import all Veir.Rewriter.Basic
import all Veir.IR.Mutators
import all Veir.IR.Basic
import all Veir.Rewriter.LinkedList.Basic
import all Veir.Rewriter.InsertPoint

public import Veir.Parser.LoweringAllocation

/-! Successful construction of fresh operations, blocks, and regions. -/

public section

namespace Veir.LLVMLowering

variable {ctx ctx' : IRContext OpCode}

theorem insertOp_total (hx : ctx.FieldsInBounds) (ho : op.InBounds ctx)
    (hb : block.InBounds ctx) (hp : op.getParent! ctx = none) :
    ∃ ctx', Rewriter.insertOp ctx op (.atEnd block) ho (by grind) hx = some ctx' := by
  let linked := op.linkBetween ctx ((InsertPoint.atEnd block).prev ctx (by grind)) none
  have hl : op.InBounds linked := by dsimp [linked]; grind
  have he : op.getParent linked hl = none := by dsimp [linked]; grind
  have hs : op.setParentWithCheck linked block hl = some (op.setParent linked (some block) hl) := by unfold OperationPtr.setParentWithCheck; rw [he]
  dsimp only [linked] at hs; unfold Rewriter.insertOp
  change ∃ ctx', op.linkBetweenWithParent ctx ((InsertPoint.atEnd block).prev ctx (by grind)) none block ho (by grind) (by simp) hb = some ctx'
  unfold OperationPtr.linkBetweenWithParent; dsimp only; split
  · rename_i hc; have h := hs.symm.trans hc; contradiction
  · split <;> exact ⟨_, rfl⟩

theorem insertBlock_total (hx : ctx.FieldsInBounds) (ho : body.InBounds ctx)
    (hb : region.InBounds ctx) (hp : body.getParent! ctx = none) :
    ∃ ctx', Rewriter.insertBlock ctx body (.atEnd region) ho (by grind) hx = some ctx' := by
  let linked := body.linkBetween ctx ((BlockInsertPoint.atEnd region).prev ctx (by grind)) none
  have hl : body.InBounds linked := by dsimp [linked]; grind
  have he : body.getParent linked hl = none := by dsimp [linked]; grind
  have hs : body.setParentWithCheck linked region hl = some (body.setParent linked (some region) hl) := by unfold BlockPtr.setParentWithCheck; rw [he]
  dsimp only [linked] at hs; unfold Rewriter.insertBlock
  change ∃ ctx', body.linkBetweenWithParent ctx ((BlockInsertPoint.atEnd region).prev ctx (by grind)) none region ho (by grind) (by simp) hb = some ctx'
  unfold BlockPtr.linkBetweenWithParent; dsimp only; split
  · rename_i hc; have h := hs.symm.trans hc; contradiction
  · split <;> exact ⟨_, rfl⟩

theorem initOpRegions_total (ho : op.InBounds ctx) (hx : ctx.FieldsInBounds)
    (hr : ∀ r ∈ rs, r.InBounds ctx) (hp : ∀ r ∈ rs, r.getParent! ctx = none)
    (hs : rs.size ≤ 1) (hn : op.getNumRegions ctx ho = 0) :
    ∃ ctx', Rewriter.initOpRegions ctx op rs (op.getNumRegions ctx ho) ho hr hx rfl = some ctx' := by
  rcases rs with ⟨xs⟩; cases xs with
  | nil => simp [Rewriter.initOpRegions, hn]
  | cons r xs => cases xs with
    | nil => simp [Rewriter.initOpRegions, hp, hn]
    | cons => simp at hs

theorem AllocationSafe.createBlock_total (h : AllocationSafe ctx) (hx : ctx.FieldsInBounds)
    (hr : region.InBounds ctx) :
    ∃ ctx' block, Rewriter.createBlock ctx ts (some (.atEnd region)) hx (by grind) = some (ctx', block) ∧ AllocationSafe ctx' := by
  obtain ⟨c, b, ha, hs⟩ := h.allocateBlock
  let body := Rewriter.initBlockArguments c b ts 0 (by grind) (by grind)
  have hs' : AllocationSafe body := hs.initBlockArguments
  obtain ⟨c', hi⟩ := insertBlock_total (ctx := body) (body := b) (region := region) (by grind) (by grind) (by grind) (by grind)
  refine ⟨c', b, ?_, hs'.insertBlock hi⟩
  unfold Rewriter.createBlock; dsimp only; split
  · rename_i hc; have he := ha.symm.trans hc; contradiction
  · rename_i c₀ b₀ hc; obtain ⟨rfl, rfl⟩ := Option.some.inj (hc.symm.trans ha); exact Option.bind_eq_some_iff.mpr ⟨c', hi, rfl⟩

theorem AllocationSafe.insertIf_total {insert : Bool} (h : AllocationSafe ctx) (hx : ctx.FieldsInBounds)
    (ho : op.InBounds ctx) (hb : insert = true → block.InBounds ctx) (hp : op.getParent! ctx = none) :
    ∃ ctx', (if hi : insert = true then Rewriter.insertOp ctx op (.atEnd block) ho (by simpa using hb hi) hx else some ctx) = some ctx' ∧ AllocationSafe ctx' := by
  cases insert
  · exact ⟨ctx, rfl, h⟩
  · obtain ⟨c, hi⟩ := insertOp_total hx ho (hb rfl) hp; exact ⟨c, hi, h.insertOp hi⟩

theorem AllocationSafe.createOp_total {insert : Bool} (h : AllocationSafe ctx) (hx : ctx.FieldsInBounds)
    {Dialect : Type} [HasOpInfo Dialect] [HasDialect OpCode Dialect]
    (code : Dialect) (props : propertiesOf code) (hb : insert = true → block.InBounds ctx)
    (hv : ∀ v ∈ vs, v.InBounds ctx) (hr : ∀ r ∈ rs, r.InBounds ctx)
    (hp : ∀ r ∈ rs, r.getParent! ctx = none) (hn : rs.size ≤ 1) :
    ∃ ctx' op, Rewriter.createOp ctx code ts vs #[] rs props
      (if insert then some (.atEnd block) else none) hv (by simp) hr (by cases insert <;> grind) hx = some (ctx', op) ∧ AllocationSafe ctx' := by
  obtain ⟨c, o, ha, hs⟩ := h.allocateOp code props
  let results := Rewriter.initOpResults c o ts 0 (by grind) (by grind)
  have hs₀ : AllocationSafe results := hs.initOpResults
  obtain ⟨c₁, hreg⟩ := initOpRegions_total (ctx := results) (op := o) (rs := rs) (by grind) (by grind) (by grind) (by grind) hn (by grind)
  let operands := Rewriter.initOpOperands c₁ o (by grind) vs (by grind) (by grind)
  let wired := Rewriter.initBlockOperands operands o #[]
  have hs₁ : AllocationSafe wired := by dsimp [wired]; unfold Rewriter.initBlockOperands; exact (hs₀.initOpRegions hreg).initOpOperands
  obtain ⟨c₂, hi, hs₂⟩ := hs₁.insertIf_total (insert := insert) (op := o) (block := block) (by grind) (by grind) (fun hi => by have := hb hi; grind) (by grind)
  refine ⟨c₂, o, ?_, hs₂⟩; unfold Rewriter.createOp; dsimp only [results, wired, operands] at *; grind

end Veir.LLVMLowering
