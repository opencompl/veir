module

public import Veir.Passes.InstructionSelection.RISCV64Branches
public import Veir.Rewriter.WfRewriter

import all Veir.Rewriter.WfRewriter.Basic
import all Veir.IR.OpCode

public section

/-!
# What the rewrites of the branch lowering leave unchanged

The branch lowering creates, erases and rewires operations. This file states
for each of these rewrites what it does to the facts that `BranchLowering`
mentions, in a form that composes over the many rewrites of the pass.
-/

namespace Veir

theorem ofDialect_cast : ofDialect OpCode Builtin.unrealized_conversion_cast =
    OpCode.builtin .unrealized_conversion_cast := by rfl

theorem ofDialect_branch : ofDialect OpCode Riscv_Cf.branch = OpCode.riscv_cf .branch := by rfl

theorem ofDialect_bnez : ofDialect OpCode Riscv_Cf.bnez = OpCode.riscv_cf .bnez := by rfl

/-! ## Replacing an element of a list by a list -/

/-- Replace every occurrence of `a` in `l` by the list `r`. -/
@[expose]
def _root_.List.replaceBy {α : Type} [DecidableEq α] (l : List α) (a : α) (r : List α) : List α :=
  l.flatMap fun b => if b = a then r else [b]

section replaceBy

variable {α : Type} [DecidableEq α] {l r r' : List α} {a x : α}

theorem _root_.List.replaceBy_self : l.replaceBy a [a] = l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [List.replaceBy, List.flatMap_cons] at ih ⊢
    rw [ih]
    by_cases hb : b = a <;> simp [hb]

theorem _root_.List.replaceBy_of_not_mem (h : a ∉ l) : l.replaceBy a r = l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    have hb : b ≠ a := fun hEq => h (by simp [hEq])
    simp only [List.replaceBy, List.flatMap_cons, hb, ↓reduceIte] at ih ⊢
    rw [ih (fun hMem => h (by simp [hMem]))]
    rfl

theorem _root_.List.replaceBy_replaceBy (h : a ∉ r) :
    (l.replaceBy a (r ++ [a])).replaceBy a r' = l.replaceBy a (r ++ r') := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [List.replaceBy, List.flatMap_cons, List.flatMap_append] at ih ⊢
    rw [ih]
    congr 1
    by_cases hb : b = a
    · have := List.replaceBy_of_not_mem (r := r') h
      simp only [List.replaceBy] at this
      simp [hb, List.flatMap_append, this]
    · simp [hb]

theorem _root_.List.insertIdx_idxOf (hNodup : l.Nodup) (hMem : a ∈ l) :
    l.insertIdx (l.idxOf a) x = l.replaceBy a [x, a] := by
  induction l with
  | nil => simp at hMem
  | cons b l ih =>
    by_cases hb : b = a
    · subst hb
      have : b ∉ l := (List.nodup_cons.mp hNodup).1
      have hRest := List.replaceBy_of_not_mem (r := [x, b]) this
      simp only [List.replaceBy] at hRest
      simp [List.replaceBy, hRest]
    · have hMem' : a ∈ l := by simpa [Ne.symm hb] using hMem
      have := ih (List.nodup_cons.mp hNodup).2 hMem'
      simp only [List.replaceBy] at this
      simp [List.replaceBy, List.idxOf_cons, hb, this]

theorem _root_.List.erase_replaceBy (hNodup : l.Nodup) (h : a ∉ r) :
    (l.replaceBy a (r ++ [a])).erase a = l.replaceBy a r := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    by_cases hb : b = a
    · subst hb
      have hNot : b ∉ l := (List.nodup_cons.mp hNodup).1
      have h₁ := List.replaceBy_of_not_mem (r := r ++ [b]) hNot
      have h₂ := List.replaceBy_of_not_mem (r := r) hNot
      simp only [List.replaceBy] at h₁ h₂
      simp only [List.replaceBy, List.flatMap_cons, ↓reduceIte, h₁, h₂, List.append_assoc]
      rw [List.erase_append_right _ h]
      simp
    · have := ih (List.nodup_cons.mp hNodup).2
      simp only [List.replaceBy] at this
      simp only [List.replaceBy, List.flatMap_cons, hb, ↓reduceIte, List.singleton_append]
      rw [List.erase_cons_tail (by simpa using hb), this]

omit [DecidableEq α] in
theorem _root_.Array.toList_eq_map_range [Inhabited α] {xs : Array α} :
    xs.toList = (List.range xs.size).map (xs[·]!) := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp only [Array.getElem_toList, List.getElem_map, List.getElem_range]
    rw [getElem!_pos xs i (by simpa using h₁)]

theorem _root_.Array.idxOf_eq_toList_idxOf {xs : Array α} : xs.idxOf a = xs.toList.idxOf a := by
  cases xs; simp

end replaceBy

/-- The facts about an operation that the description of the lowering mentions. -/
structure OpSame (f : ValuePtr → ValuePtr) (ctx ctx' : IRContext OpCode) (op : OperationPtr) :
    Prop where
  inBounds : op.InBounds ctx'
  opType : op.getOpType! ctx' = op.getOpType! ctx
  properties : ∀ {Dialect : Type} [HasOpInfo Dialect] [HasDialect OpCode Dialect]
    (opCode : Dialect), op.getProperties! ctx' opCode = op.getProperties! ctx opCode
  resultTypes : op.getResultTypes! ctx' = op.getResultTypes! ctx
  /-- The operands are the same up to `f`. -/
  operands : op.getOperands! ctx' = (op.getOperands! ctx).map f
  successors : op.getSuccessors! ctx' = op.getSuccessors! ctx
  numRegions : op.getNumRegions! ctx' = op.getNumRegions! ctx
  region : ∀ i, op.getRegion! ctx' i = op.getRegion! ctx i
  parent : (op.get! ctx').parent = (op.get! ctx).parent

/-- The facts about blocks and regions that the description of the lowering mentions. -/
structure CtxSame (ctx ctx' : IRContext OpCode) : Prop where
  blockIn : ∀ {block : BlockPtr}, block.InBounds ctx → block.InBounds ctx'
  numArguments : ∀ {block : BlockPtr}, block.InBounds ctx →
    block.getNumArguments! ctx' = block.getNumArguments! ctx
  blockParent : ∀ {block : BlockPtr}, block.InBounds ctx →
    (block.get! ctx').parent = (block.get! ctx).parent
  regionIn : ∀ {region : RegionPtr}, region.InBounds ctx → region.InBounds ctx'
  firstBlock : ∀ {region : RegionPtr}, region.InBounds ctx →
    (region.get! ctx').firstBlock = (region.get! ctx).firstBlock
  regionParent : ∀ {region : RegionPtr}, region.InBounds ctx →
    (region.get! ctx').parent = (region.get! ctx).parent

theorem OpSame.refl {ctx : IRContext OpCode} {op : OperationPtr} (opIn : op.InBounds ctx) :
    OpSame id ctx ctx op :=
  ⟨opIn, rfl, fun _ => rfl, rfl, by simp, rfl, rfl, fun _ => rfl, rfl⟩

theorem OpSame.trans {f g : ValuePtr → ValuePtr} {ctx₁ ctx₂ ctx₃ : IRContext OpCode}
    {op : OperationPtr} (h₁ : OpSame f ctx₁ ctx₂ op) (h₂ : OpSame g ctx₂ ctx₃ op) :
    OpSame (g ∘ f) ctx₁ ctx₃ op :=
  ⟨h₂.inBounds, h₂.opType.trans h₁.opType, fun c => (h₂.properties c).trans (h₁.properties c),
    h₂.resultTypes.trans h₁.resultTypes, by rw [h₂.operands, h₁.operands]; simp,
    h₂.successors.trans h₁.successors, h₂.numRegions.trans h₁.numRegions,
    fun i => (h₂.region i).trans (h₁.region i), h₂.parent.trans h₁.parent⟩

theorem OpSame.trans_id {f : ValuePtr → ValuePtr} {ctx₁ ctx₂ ctx₃ : IRContext OpCode}
    {op : OperationPtr} (h₁ : OpSame f ctx₁ ctx₂ op) (h₂ : OpSame id ctx₂ ctx₃ op) :
    OpSame f ctx₁ ctx₃ op := by
  simpa using h₁.trans h₂

theorem CtxSame.refl {ctx : IRContext OpCode} : CtxSame ctx ctx :=
  ⟨id, fun _ => rfl, fun _ => rfl, id, fun _ => rfl, fun _ => rfl⟩

theorem CtxSame.trans {ctx₁ ctx₂ ctx₃ : IRContext OpCode} (h₁ : CtxSame ctx₁ ctx₂)
    (h₂ : CtxSame ctx₂ ctx₃) : CtxSame ctx₁ ctx₃ :=
  ⟨fun h => h₂.blockIn (h₁.blockIn h),
    fun h => (h₂.numArguments (h₁.blockIn h)).trans (h₁.numArguments h),
    fun h => (h₂.blockParent (h₁.blockIn h)).trans (h₁.blockParent h),
    fun h => h₂.regionIn (h₁.regionIn h),
    fun h => (h₂.firstBlock (h₁.regionIn h)).trans (h₁.firstBlock h),
    fun h => (h₂.regionParent (h₁.regionIn h)).trans (h₁.regionParent h)⟩

/-! ## Creating an operation -/

section createOp

variable {Dialect : Type} [HasOpInfo Dialect] [HasDialect OpCode Dialect]
variable {ctx ctx' : WfIRContext OpCode} {opType : Dialect} {resultTypes : Array TypeAttr}
  {operands : Array ValuePtr} {successors : Array BlockPtr} {properties : propertiesOf opType}
  {ip : InsertPoint} {newOp : OperationPtr}

/-- A successful `createOp!` is a `createOp`. -/
theorem WfRewriter.createOp_of_createOp!
    (h : WfRewriter.createOp! ctx opType resultTypes operands successors #[] properties (some ip) =
      some (ctx', newOp)) :
    ∃ h₁ h₂ h₃ h₄, WfRewriter.createOp ctx opType resultTypes operands successors #[] properties
      (some ip) h₁ h₂ h₃ h₄ = some (ctx', newOp) := by
  unfold WfRewriter.createOp! at h
  split at h
  next h₁ =>
    split at h
    next h₂ =>
      split at h
      next h₃ =>
        simp only at h
        split at h
        next h₄ =>
          split at h
          next result hResult => exact ⟨h₁, h₂, h₃, by grind, by rw [hResult, h]⟩
          next => simp at h
        next => simp at h
      next => simp at h
    next => simp at h
  next => simp at h

/-- What creating an operation in front of an insertion point does. -/
theorem WfRewriter.createOp_frame {h₁ h₂ h₃ h₄}
    (h : WfRewriter.createOp ctx opType resultTypes operands successors #[] properties (some ip)
      h₁ h₂ h₃ h₄ = some (ctx', newOp)) :
    ¬ newOp.InBounds ctx.raw ∧ newOp.InBounds ctx'.raw ∧
    (∀ op, op.InBounds ctx.raw → OpSame id ctx.raw ctx'.raw op) ∧
    CtxSame ctx.raw ctx'.raw ∧
    (∀ value : ValuePtr, value.InBounds ctx.raw →
      value.getType! ctx'.raw = value.getType! ctx.raw) ∧
    newOp.getOpType! ctx'.raw = ofDialect OpCode opType ∧
    newOp.getResultTypes! ctx'.raw = resultTypes ∧
    newOp.getOperands! ctx'.raw = operands ∧
    newOp.getSuccessors! ctx'.raw = successors := by
  have hNotIn := WfRewriter.createOp_new_not_inBounds newOp h
  refine ⟨hNotIn, WfRewriter.createOp_new_inBounds newOp h, fun op opIn => ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · have hNe : op ≠ newOp := fun hEq => hNotIn (hEq ▸ opIn)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := WfRewriter.createOp_inBounds_mono (ptr := GenericPtr.operation op) h
      grind
    · rw [OperationPtr.getOpType!_WfRewriter_createOp h]; simp [hNe]
    · intro D _ _ c; rw [OperationPtr.getProperties!_WfRewriter_createOp h]; simp [hNe]
    · rw [OperationPtr.getResultTypes!_WfRewriter_createOp h]; simp [hNe]
    · rw [OperationPtr.getOperands!_WfRewriter_createOp h]; simp [hNe]
    · rw [OperationPtr.getSuccessors!_WfRewriter_createOp h]; simp [hNe]
    · rw [OperationPtr.getNumRegions!_WfRewriter_createOp h]; simp [hNe]
    · intro i; rw [OperationPtr.getRegion!_WfRewriter_createOp h]; simp [hNe]
    · rw [OperationPtr.parent!_WfRewriter_createOp h]; simp [hNe]
  · refine ⟨fun {block} hb => ?_, fun _ => ?_, fun _ => ?_, fun {region} hr => ?_, fun _ => ?_,
      fun _ => ?_⟩
    · have := WfRewriter.createOp_inBounds_mono (ptr := GenericPtr.block block) h; grind
    · exact BlockPtr.getNumArguments!_WfRewriter_createOp h
    · exact BlockPtr.parent!_WfRewriter_createOp h
    · have := WfRewriter.createOp_inBounds_mono (ptr := GenericPtr.region region) h; grind
    · exact RegionPtr.firstBlock!_WfRewriter_createOp h
    · rw [RegionPtr.parent!_WfRewriter_createOp h]; simp
  · intro value valueIn
    rw [ValuePtr.getType!_WfRewriter_createOp h]
    rcases value with result | arg
    · have : result.op ≠ newOp := fun hEq => hNotIn (hEq ▸ by
        obtain ⟨opIn, _⟩ := OpResultPtr.inBounds_def.mp (by simpa using valueIn); exact opIn)
      simp [this]
    · rfl
  · rw [OperationPtr.getOpType!_WfRewriter_createOp h]; simp
  · rw [OperationPtr.getResultTypes!_WfRewriter_createOp h]; simp
  · rw [OperationPtr.getOperands!_WfRewriter_createOp h]; simp
  · rw [OperationPtr.getSuccessors!_WfRewriter_createOp h]; simp

/-- A `riscv_cf.bnez` that was created has the properties it was created with. -/
theorem WfRewriter.createOp_bnez_properties {ctx ctx' : WfIRContext OpCode}
    {resultTypes : Array TypeAttr} {operands : Array ValuePtr} {successors : Array BlockPtr}
    {properties : RISCVBrProperties} {ip : InsertPoint} {newOp : OperationPtr} {h₁ h₂ h₃ h₄}
    (h : WfRewriter.createOp ctx Riscv_Cf.bnez resultTypes operands successors #[] properties
      (some ip) h₁ h₂ h₃ h₄ = some (ctx', newOp)) :
    newOp.getProperties! ctx'.raw (OpCode.riscv_cf .bnez) = properties := by
  rw [OperationPtr.getProperties!_WfRewriter_createOp h]
  simp only [↓reduceIte]
  have hEq : ofDialect OpCode Riscv_Cf.bnez = ofDialect OpCode (OpCode.riscv_cf Riscv_Cf.bnez) := by
    rfl
  exact dite_eq_left_of_eq_true (eq_true hEq)

/-- The operations of a block, as a list. -/
noncomputable abbrev _root_.Veir.BlockPtr.opList (block : BlockPtr) (ctx : WfIRContext OpCode)
    (blockIn : block.InBounds ctx.raw) : List OperationPtr :=
  (block.operationList ctx.raw ctx.wellFormed blockIn).toList

theorem _root_.Veir.BlockPtr.opList_nodup {block : BlockPtr} {ctx : WfIRContext OpCode}
    {blockIn : block.InBounds ctx.raw} : (block.opList ctx blockIn).Nodup :=
  BlockPtr.OpChain_array_toList_Nodup (BlockPtr.operationListWF ctx.raw block blockIn ctx.wellFormed)

theorem _root_.Veir.BlockPtr.mem_opList {block : BlockPtr} {ctx : WfIRContext OpCode}
    {blockIn : block.InBounds ctx.raw} {op : OperationPtr} (opIn : op.InBounds ctx.raw) :
    op ∈ block.opList ctx blockIn ↔ (op.get! ctx.raw).parent = some block := by
  rw [BlockPtr.operationList.mem opIn (hctx := ctx.wellFormed) (hblock := blockIn)]
  simp [BlockPtr.opList]

/-- Creating an operation in front of `op` puts it in front of `op` in the list of its block. -/
theorem WfRewriter.createOp_before_opList {op : OperationPtr} {h₁ h₂ h₃ h₄}
    (h : WfRewriter.createOp ctx opType resultTypes operands successors #[] properties
      (some (.before op)) h₁ h₂ h₃ h₄ = some (ctx', newOp))
    {block : BlockPtr} (blockIn : block.InBounds ctx.raw) (blockIn' : block.InBounds ctx'.raw) :
    block.opList ctx' blockIn' = (block.opList ctx blockIn).replaceBy op [newOp, op] := by
  have opIn : op.InBounds ctx.raw := by grind
  simp only [WfRewriter.createOp] at h
  split at h
  next => simp at h
  next raw' newOp' hRaw =>
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [BlockPtr.opList]
    rw [BlockPtr.operationList_rewriter_createOp hRaw ctx.wellFormed]
    simp only [InsertPoint.block!_before_eq]
    split
    next hParent =>
      simp only [InsertPoint.idxIn_before_eq, Array.toList_insertIdx, Array.idxOf_eq_toList_idxOf]
      exact List.insertIdx_idxOf BlockPtr.opList_nodup ((BlockPtr.mem_opList opIn).mpr hParent)
    next hParent =>
      rw [List.replaceBy_of_not_mem]
      exact fun hMem => hParent ((BlockPtr.mem_opList opIn).mp hMem)

end createOp

/-! ## Erasing an operation -/

section eraseOp

variable {ctx : WfIRContext OpCode} {op : OperationPtr}

/-- An `eraseOp!` whose conditions hold is an `eraseOp`. -/
theorem WfRewriter.eraseOp!_eq (opIn : op.InBounds ctx.raw)
    (hRegions : op.getNumRegions! ctx.raw = 0) (hUses : (!op.hasUses! ctx.raw) = true) :
    WfRewriter.eraseOp! ctx op = WfRewriter.eraseOp ctx op hRegions hUses opIn := by
  simp [WfRewriter.eraseOp!, opIn, hRegions, hUses]

/-- What erasing an operation does. -/
theorem WfRewriter.eraseOp_frame {hRegions hUses} {opIn : op.InBounds ctx.raw} :
    let ctx' := WfRewriter.eraseOp ctx op hRegions hUses opIn
    (∀ op', op'.InBounds ctx.raw → op' ≠ op → OpSame id ctx.raw ctx'.raw op') ∧
    CtxSame ctx.raw ctx'.raw ∧
    (∀ value : ValuePtr, value.InBounds ctx'.raw →
      value.getType! ctx'.raw = value.getType! ctx.raw) ∧
    (∀ value : ValuePtr, value.InBounds ctx.raw → (∀ r, value = .opResult r → r.op ≠ op) →
      value.InBounds ctx'.raw) := by
  intro ctx'
  have hIn : ∀ ptr : GenericPtr, (match ptr with
      | .operation op' => op' ≠ op
      | .opResult or => or.op ≠ op
      | .opOperand oo => oo.op ≠ op
      | .blockOperand bo => bo.op ≠ op
      | .value (.opResult or) => or.op ≠ op
      | .opOperandPtr (.operandNextUse oo) => oo.op ≠ op
      | .opOperandPtr (.valueFirstUse (.opResult or)) => or.op ≠ op
      | .blockOperandPtr (.blockOperandNextUse oo) => oo.op ≠ op
      | _ => True) → (ptr.InBounds ctx'.raw ↔ ptr.InBounds ctx.raw) := fun ptr hPtr =>
    Rewriter.eraseOp_inBounds ptr hPtr
  refine ⟨fun op' opIn' hNe => ?_, ?_, fun value valueIn =>
    ValuePtr.getType!_wfRewriter_eraseOp valueIn, fun value valueIn hValue => ?_⟩
  · have opIn'' : op'.InBounds ctx'.raw := by
      have := hIn (.operation op') hNe; grind
    exact ⟨opIn'', OperationPtr.getOpType!_wfRewriter_eraseOp opIn'',
      fun _ => OperationPtr.getProperties!_wfRewriter_eraseOp opIn'',
      OperationPtr.getResultTypes!_wfRewriter_eraseOp opIn'',
      by rw [OperationPtr.getOperands!_wfRewriter_eraseOp opIn'']; simp,
      OperationPtr.getSuccessors!_wfRewriter_eraseOp opIn'',
      OperationPtr.getNumRegions!_wfRewriter_eraseOp opIn'',
      fun _ => OperationPtr.getRegion!_wfRewriter_eraseOp opIn'',
      by rw [OperationPtr.parent!_wfRewriter_eraseOp opIn'']; simp [hNe]⟩
  · refine ⟨fun {block} hb => ?_, fun _ => ?_, fun _ => ?_, fun {region} hr => ?_, fun _ => ?_,
      fun _ => ?_⟩
    · have := hIn (.block block) trivial; grind
    · simp [ctx']
    · simp [ctx']
    · have := hIn (.region region) trivial; grind
    · simp [ctx']
    · simp [ctx']
  · have := hIn (.value value) (by
      rcases value with r | a
      · exact hValue r rfl
      · trivial)
    grind

/-- Erasing an operation removes it from the list of its block. -/
theorem WfRewriter.eraseOp_opList {hRegions hUses} {opIn : op.InBounds ctx.raw} {block : BlockPtr}
    (blockIn : block.InBounds ctx.raw)
    (blockIn' : block.InBounds (WfRewriter.eraseOp ctx op hRegions hUses opIn).raw) :
    block.opList (WfRewriter.eraseOp ctx op hRegions hUses opIn) blockIn' =
      (block.opList ctx blockIn).erase op := by
  simp only [BlockPtr.opList, WfRewriter.eraseOp]
  rw [BlockPtr.operationList_rewriter_eraseOp ctx.wellFormed]
  split
  next hParent => simp
  next hParent =>
    rw [List.erase_of_not_mem]
    exact fun hMem => hParent ((BlockPtr.mem_opList opIn).mp hMem)

end eraseOp

end Veir
