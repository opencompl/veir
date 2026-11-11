module

public import Veir.Passes.LLVMToGMIR.BranchSimulation
public import Veir.Passes.InstructionSelection.Branches.Pass

import all Veir.Passes.LLVMToGMIR.Branches
import all Veir.IR.Basic
import all Veir.IR.OpCode

public section

/-!
# The branch step computes a branch translation

`convertLLVMBranches` succeeds only with a module that is the
`LLVMBranchTranslation` of its input, so the module it returns refines the
input, if the operations of the input are monotone in CTrees.
-/

namespace Veir

theorem ofDialect_gmir (op : GMIR) : ofDialect OpCode op = OpCode.gmir op := by rfl

/-- A gMIR operation that was created has the properties it was created with. -/
theorem WfRewriter.createOp_gmir_properties {ctx ctx' : WfIRContext OpCode} {op : GMIR}
    {resultTypes : Array TypeAttr} {operands : Array ValuePtr} {successors : Array BlockPtr}
    {properties : GMIR.propertiesOf op} {ip : InsertPoint} {newOp : OperationPtr} {h₁ h₂ h₃ h₄}
    (h : WfRewriter.createOp ctx op resultTypes operands successors #[] properties
      (some ip) h₁ h₂ h₃ h₄ = some (ctx', newOp)) :
    newOp.getProperties! ctx'.raw (OpCode.gmir op) = properties := by
  rw [OperationPtr.getProperties!_WfRewriter_createOp h]
  simp only [↓reduceIte]
  have hEq : ofDialect OpCode op = ofDialect OpCode (OpCode.gmir op) := by
    rfl
  exact dite_eq_left_of_eq_true (eq_true hEq)

/-- Replacing every occurrence of `a` by `b` maps the list. -/
theorem _root_.List.replaceBy_singleton {α : Type} [DecidableEq α] {l : List α} {a b : α} :
    l.replaceBy a [b] = l.map fun x => if x = a then b else x := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.replaceBy, List.flatMap_cons, List.map_cons] at ih ⊢
    rw [ih]
    by_cases hx : x = a <;> simp [hx]

/-! ## Replacing one branch -/

/-- What replacing the LLVM branch `op` by the gMIR branch `newOp` does. -/
structure LLVMBranchStep (ctx ctx' : WfIRContext OpCode) (op newOp : OperationPtr) : Prop where
  ops : ∀ o, o.InBounds ctx.raw → o ≠ op → OpSame id ctx.raw ctx'.raw o
  ctxSame : CtxSame ctx.raw ctx'.raw
  types : ∀ value : ValuePtr, value.InBounds ctx.raw → (∀ r, value = .opResult r → r.op ≠ op) →
    value.InBounds ctx'.raw ∧ value.getType! ctx'.raw = value.getType! ctx.raw
  newIn : newOp.InBounds ctx'.raw
  newNotIn : ¬ newOp.InBounds ctx.raw
  newResultTypes : newOp.getResultTypes! ctx'.raw = #[]
  newOperands : newOp.getOperands! ctx'.raw = op.getOperands! ctx.raw
  newSuccessors : newOp.getSuccessors! ctx'.raw = op.getSuccessors! ctx.raw
  newBr : op.getOpType! ctx.raw = .llvm .br → newOp.getOpType! ctx'.raw = .gmir .g_br
  newBrCond : op.getOpType! ctx.raw = .llvm .cond_br →
    newOp.getOpType! ctx'.raw = .gmir .g_brcond ∧
    (newOp.getProperties! ctx'.raw (OpCode.gmir .g_brcond)).operandSegmentSizes =
      (op.getProperties! ctx.raw (OpCode.llvm .cond_br)).operandSegmentSizes
  opList : ∀ (block : BlockPtr) (blockIn : block.InBounds ctx.raw),
    block.opList ctx' (ctxSame.blockIn blockIn) = (block.opList ctx blockIn).replaceBy op [newOp]

/-- The step from the creation of the new branch in front of `op`, and the erasure of `op`. -/
theorem LLVMBranchStep.of_frames {ctx ctx₂ ctx' : WfIRContext OpCode} {op newOp : OperationPtr}
    (opIn : op.InBounds ctx.raw)
    (hNotIn : ¬ newOp.InBounds ctx.raw) (hIn : newOp.InBounds ctx₂.raw)
    (hOps : ∀ o, o.InBounds ctx.raw → OpSame id ctx.raw ctx₂.raw o)
    (hCtx : CtxSame ctx.raw ctx₂.raw)
    (hTypes : ∀ value : ValuePtr, value.InBounds ctx.raw →
      value.getType! ctx₂.raw = value.getType! ctx.raw)
    (hMono : ∀ ptr : GenericPtr, ptr.InBounds ctx.raw → ptr.InBounds ctx₂.raw)
    (hResultTypes : newOp.getResultTypes! ctx₂.raw = #[])
    (hOperands : newOp.getOperands! ctx₂.raw = op.getOperands! ctx.raw)
    (hSuccessors : newOp.getSuccessors! ctx₂.raw = op.getSuccessors! ctx.raw)
    (hBr : op.getOpType! ctx.raw = .llvm .br → newOp.getOpType! ctx₂.raw = .gmir .g_br)
    (hBrCond : op.getOpType! ctx.raw = .llvm .cond_br →
      newOp.getOpType! ctx₂.raw = .gmir .g_brcond ∧
      (newOp.getProperties! ctx₂.raw (OpCode.gmir .g_brcond)).operandSegmentSizes =
        (op.getProperties! ctx.raw (OpCode.llvm .cond_br)).operandSegmentSizes)
    (hList : ∀ (block : BlockPtr) (blockIn : block.InBounds ctx.raw)
      (blockIn₂ : block.InBounds ctx₂.raw),
      block.opList ctx₂ blockIn₂ = (block.opList ctx blockIn).replaceBy op [newOp, op])
    (hResults₀ : op.getNumResults! ctx.raw = 0) (hRegions₀ : op.getNumRegions! ctx.raw = 0)
    (hErase : ctx' = WfRewriter.eraseOp! ctx₂ op) :
    LLVMBranchStep ctx ctx' op newOp := by
  subst hErase
  have hSameOp := hOps op opIn
  have opIn₂ : op.InBounds ctx₂.raw := hSameOp.inBounds
  have hRegions : op.getNumRegions! ctx₂.raw = 0 := by
    rw [hSameOp.numRegions]; exact hRegions₀
  have hUses : op.hasUses! ctx₂.raw = false := by
    have : op.getNumResults! ctx₂.raw = 0 := by
      rw [← OperationPtr.getResultTypes!.size_eq_getNumResults!, hSameOp.resultTypes,
        OperationPtr.getResultTypes!.size_eq_getNumResults!]
      exact hResults₀
    rw [Bool.eq_false_iff, ne_eq, OperationPtr.hasUses!_eq_true_iff_hasUses!_getResult]
    simp [this]
  rw [WfRewriter.eraseOp!_eq opIn₂ hRegions (by simp [hUses])]
  obtain ⟨hOps₃, hCtx₃, hTypes₃, hValues₃⟩ := WfRewriter.eraseOp_frame (ctx := ctx₂) (op := op)
    (hRegions := hRegions) (hUses := by simp [hUses]) (opIn := opIn₂)
  have hNewNe : newOp ≠ op := fun hEq => hNotIn (hEq ▸ opIn)
  have hNewSame := hOps₃ newOp hIn hNewNe
  refine {
    ops := fun o oIn hNe => (hOps o oIn).trans_id (hOps₃ o (hOps o oIn).inBounds hNe)
    ctxSame := hCtx.trans hCtx₃
    types := fun v vIn hv => ?_
    newIn := hNewSame.inBounds
    newNotIn := hNotIn
    newResultTypes := hNewSame.resultTypes.trans hResultTypes
    newOperands := by rw [hNewSame.operands, hOperands]; simp
    newSuccessors := hNewSame.successors.trans hSuccessors
    newBr := fun h => hNewSame.opType.trans (hBr h)
    newBrCond := fun h => ⟨hNewSame.opType.trans (hBrCond h).1,
      by rw [hNewSame.properties]; exact (hBrCond h).2⟩
    opList := fun block blockIn => ?_ }
  · have h₂ : v.InBounds ctx₂.raw := by simpa using hMono (.value v) (by simpa using vIn)
    have h₃ := hValues₃ v h₂ hv
    exact ⟨h₃, (hTypes₃ v h₃).trans (hTypes v vIn)⟩
  · have blockIn₂ := hCtx.blockIn blockIn
    rw [WfRewriter.eraseOp_opList blockIn₂, hList block blockIn blockIn₂,
      show [newOp, op] = [newOp] ++ [op] by simp,
      List.erase_replaceBy BlockPtr.opList_nodup (by simpa using hNewNe.symm)]

/-- What `convertLLVMBranch` leaves behind. -/
theorem convertLLVMBranch_ok {ctx ctx' : WfIRContext OpCode} {op : OperationPtr}
    (opIn : op.InBounds ctx.raw) (h : convertLLVMBranch ctx op = .ok ctx') :
    (¬ op.IsLLVMBranch ctx.raw ∧ ctx' = ctx) ∨
    (op.IsLLVMBranch ctx.raw ∧ op.getNumResults! ctx.raw = 0 ∧
      ∃ newOp, LLVMBranchStep ctx ctx' op newOp) := by
  simp only [convertLLVMBranch, bind, Except.bind] at h
  split at h
  next hBranch =>
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact .inl ⟨hBranch, h.symm⟩
  next hBranch =>
    have hBranch : op.IsLLVMBranch ctx.raw := Decidable.not_not.mp hBranch
    split at h
    next => simp [throw, throwThe, MonadExceptOf.throw] at h
    next hCounts =>
      simp only [not_or, Decidable.not_not] at hCounts
      refine .inr ⟨hBranch, hCounts.1, ?_⟩
      split at h
      next ctx₂ newOp hCreate =>
        simp only [pure, Except.pure, Except.ok.injEq] at h
        refine ⟨newOp, ?_⟩
        simp only [createGMIRBranch] at hCreate
        split at hCreate
        next hType =>
          obtain ⟨h₁, h₂, h₃, h₄, hCreate⟩ := WfRewriter.createOp_of_createOp! hCreate
          obtain ⟨hNotIn, hIn, hOps, hCtx, hTypes, hNewType, hResultTypes, hOperands,
            hSuccessors⟩ := WfRewriter.createOp_frame hCreate
          exact LLVMBranchStep.of_frames opIn hNotIn hIn hOps hCtx hTypes
            (fun ptr => WfRewriter.createOp_inBounds_mono hCreate) hResultTypes hOperands
            hSuccessors (fun _ => hNewType.trans (ofDialect_gmir _))
            (fun h' => by rw [hType] at h'; cases h')
            (fun block blockIn blockIn₂ =>
              WfRewriter.createOp_before_opList hCreate blockIn blockIn₂)
            hCounts.1 hCounts.2 h.symm
        next hType =>
          obtain ⟨h₁, h₂, h₃, h₄, hCreate⟩ := WfRewriter.createOp_of_createOp! hCreate
          have hProps := WfRewriter.createOp_gmir_properties hCreate
          obtain ⟨hNotIn, hIn, hOps, hCtx, hTypes, hNewType, hResultTypes, hOperands,
            hSuccessors⟩ := WfRewriter.createOp_frame hCreate
          exact LLVMBranchStep.of_frames opIn hNotIn hIn hOps hCtx hTypes
            (fun ptr => WfRewriter.createOp_inBounds_mono hCreate) hResultTypes hOperands
            hSuccessors (fun h' => absurd h' hType)
            (fun _ => ⟨hNewType.trans (ofDialect_gmir _), by rw [hProps]⟩)
            (fun block blockIn blockIn₂ =>
              WfRewriter.createOp_before_opList hCreate blockIn blockIn₂)
            hCounts.1 hCounts.2 h.symm
      next => simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ## Replacing all branches -/

/-- What the replacement of the branch `op` of `ctx₀` by `newOp` left in `ctx`. -/
structure ReplacedBranch (ctx₀ ctx : WfIRContext OpCode) (op newOp : OperationPtr) : Prop where
  numResults : op.getNumResults! ctx₀.raw = 0
  newIn : newOp.InBounds ctx.raw
  newResultTypes : newOp.getResultTypes! ctx.raw = #[]
  newOperands : newOp.getOperands! ctx.raw = op.getOperands! ctx₀.raw
  newSuccessors : newOp.getSuccessors! ctx.raw = op.getSuccessors! ctx₀.raw
  newBr : op.getOpType! ctx₀.raw = .llvm .br → newOp.getOpType! ctx.raw = .gmir .g_br
  newBrCond : op.getOpType! ctx₀.raw = .llvm .cond_br →
    newOp.getOpType! ctx.raw = .gmir .g_brcond ∧
    (newOp.getProperties! ctx.raw (OpCode.gmir .g_brcond)).operandSegmentSizes =
      (op.getProperties! ctx₀.raw (OpCode.llvm .cond_br)).operandSegmentSizes

/-- A new branch that stays the same stays a replacement. -/
theorem ReplacedBranch.mono {ctx₀ ctx ctx' : WfIRContext OpCode} {op newOp : OperationPtr}
    (h : ReplacedBranch ctx₀ ctx op newOp) (hSame : OpSame id ctx.raw ctx'.raw newOp) :
    ReplacedBranch ctx₀ ctx' op newOp :=
  ⟨h.numResults, hSame.inBounds, hSame.resultTypes.trans h.newResultTypes,
    by rw [hSame.operands, h.newOperands]; simp, hSame.successors.trans h.newSuccessors,
    fun hB => hSame.opType.trans (h.newBr hB),
    fun hB => ⟨hSame.opType.trans (h.newBrCond hB).1,
      by rw [hSame.properties]; exact (h.newBrCond hB).2⟩⟩

/-- The replacement of a branch is not an LLVM branch. -/
theorem ReplacedBranch.not_isLLVMBranch {ctx₀ ctx : WfIRContext OpCode} {op newOp : OperationPtr}
    (h : ReplacedBranch ctx₀ ctx op newOp) (hBranch : op.IsLLVMBranch ctx₀.raw) :
    ¬ newOp.IsLLVMBranch ctx.raw := by
  rcases hBranch with hB | hB
  · simp [OperationPtr.IsLLVMBranch, h.newBr hB]
  · simp [OperationPtr.IsLLVMBranch, (h.newBrCond hB).1]

/-- Whether `o` is a branch among `done`, which the step has replaced. -/
abbrev Replaced (ctx₀ : IRContext OpCode) (done : List OperationPtr) (o : OperationPtr) : Prop :=
  o ∈ done ∧ o.IsLLVMBranch ctx₀

/-- The module after the branches among `done` were replaced. -/
structure TranslationInv (ctx₀ ctx : WfIRContext OpCode) (done : List OperationPtr)
    (newBranch : OperationPtr → OperationPtr) : Prop where
  ops : ∀ o, o.InBounds ctx₀.raw → ¬ Replaced ctx₀.raw done o → OpSame id ctx₀.raw ctx.raw o
  ctxSame : CtxSame ctx₀.raw ctx.raw
  types : ∀ value : ValuePtr, value.InBounds ctx₀.raw →
    value.InBounds ctx.raw ∧ value.getType! ctx.raw = value.getType! ctx₀.raw
  branch : ∀ o, Replaced ctx₀.raw done o → ReplacedBranch ctx₀ ctx o (newBranch o)
  opList : ∀ (block : BlockPtr) (blockIn : block.InBounds ctx₀.raw),
    block.opList ctx (ctxSame.blockIn blockIn) =
      (block.opList ctx₀ blockIn).map fun o =>
        if Replaced ctx₀.raw done o then newBranch o else o

theorem TranslationInv.init {ctx₀ : WfIRContext OpCode} {newBranch} :
    TranslationInv ctx₀ ctx₀ [] newBranch :=
  ⟨fun _ oIn _ => OpSame.refl oIn, CtxSame.refl, fun _ vIn => ⟨vIn, rfl⟩,
    fun _ h => (List.not_mem_nil h.1).elim, fun _ _ => by simp [Replaced]⟩

theorem TranslationInv.step {ctx₀ ctx ctx' : WfIRContext OpCode} {done : List OperationPtr}
    {newBranch} {op : OperationPtr} (hInv : TranslationInv ctx₀ ctx done newBranch)
    (opIn₀ : op.InBounds ctx₀.raw) (hNotDone : op ∉ done)
    (h : convertLLVMBranch ctx op = .ok ctx') :
    ∃ newBranch', TranslationInv ctx₀ ctx' (op :: done) newBranch' := by
  have hSame := hInv.ops op opIn₀ (fun h => hNotDone h.1)
  have hBranchIff : op.IsLLVMBranch ctx.raw ↔ op.IsLLVMBranch ctx₀.raw := by
    simp [OperationPtr.IsLLVMBranch, hSame.opType]
  rcases convertLLVMBranch_ok hSame.inBounds h with
    ⟨hBranch, rfl⟩ | ⟨hBranch, hResults, newOp, hStep⟩
  · /- Not a branch: nothing changes. -/
    have hBranch₀ : ¬ op.IsLLVMBranch ctx₀.raw := by rwa [← hBranchIff]
    have hIff : ∀ o, Replaced ctx₀.raw (op :: done) o ↔ Replaced ctx₀.raw done o := by
      intro o
      simp only [Replaced, List.mem_cons]
      constructor
      · rintro ⟨rfl | hMem, hB⟩
        · exact absurd hB hBranch₀
        · exact ⟨hMem, hB⟩
      · exact fun ⟨hMem, hB⟩ => ⟨.inr hMem, hB⟩
    refine ⟨newBranch, fun o oIn hNot => hInv.ops o oIn (by rwa [← hIff]), hInv.ctxSame,
      hInv.types, fun o hR => hInv.branch o ((hIff o).mp hR), fun block blockIn => ?_⟩
    rw [hInv.opList block blockIn]
    simp only [hIff]
  /- A branch: it is replaced by `newOp`. -/
  have hBranch₀ : op.IsLLVMBranch ctx₀.raw := hBranchIff.mp hBranch
  have hResults₀ : op.getNumResults! ctx₀.raw = 0 := by
    rw [← OperationPtr.getResultTypes!.size_eq_getNumResults!, ← hSame.resultTypes,
      OperationPtr.getResultTypes!.size_eq_getNumResults!, hResults]
  /- No new branch of an earlier step is the branch replaced now, which is an LLVM branch. -/
  have hNe : ∀ o, Replaced ctx₀.raw done o → newBranch o ≠ op := fun o hR hEq =>
    (hInv.branch o hR).not_isLLVMBranch hR.2 (hEq ▸ hBranch)
  refine ⟨fun o => if o = op then newOp else newBranch o, fun o oIn hNot => ?_,
    hInv.ctxSame.trans hStep.ctxSame, fun v vIn => ?_, fun o hR => ?_, fun block blockIn => ?_⟩
  · have hNe' : o ≠ op := fun hEq => hNot ⟨by simp [hEq], hEq ▸ hBranch₀⟩
    have hOld := hInv.ops o oIn (fun h => hNot ⟨List.mem_cons_of_mem _ h.1, h.2⟩)
    exact hOld.trans_id (hStep.ops o hOld.inBounds hNe')
  · have h₁ := hInv.types v vIn
    have h₂ := hStep.types v h₁.1 (fun r hr hEq => by
      subst hr
      obtain ⟨_, hIndex⟩ := OpResultPtr.inBounds_def.mp (by simpa using h₁.1)
      grind)
    exact ⟨h₂.1, h₂.2.trans h₁.2⟩
  · by_cases hEq : o = op
    · subst hEq
      simp only [↓reduceIte]
      exact ⟨hResults₀, hStep.newIn, hStep.newResultTypes,
        hStep.newOperands.trans (by rw [hSame.operands]; simp), hStep.newSuccessors.trans
        hSame.successors, fun hB => hStep.newBr (hSame.opType.trans hB),
        fun hB => ⟨(hStep.newBrCond (hSame.opType.trans hB)).1,
          by rw [(hStep.newBrCond (hSame.opType.trans hB)).2, hSame.properties]⟩⟩
    · have hR' : Replaced ctx₀.raw done o := ⟨by simpa [hEq] using hR.1, hR.2⟩
      have hOld := hInv.branch o hR'
      simp only [hEq, ↓reduceIte]
      exact hOld.mono (hStep.ops _ hOld.newIn (hNe o hR'))
  · rw [hStep.opList block (hInv.ctxSame.blockIn blockIn), hInv.opList block blockIn,
      List.replaceBy_singleton, List.map_map]
    refine List.map_congr_left fun o _ => ?_
    simp only [Function.comp_apply]
    by_cases hEq : o = op
    · subst hEq
      simp [Replaced, hNotDone, hBranch₀]
    · by_cases hR : Replaced ctx₀.raw done o
      · have hR' : Replaced ctx₀.raw (op :: done) o := ⟨List.mem_cons_of_mem _ hR.1, hR.2⟩
        have hNe' := hNe o hR
        simp only [Replaced] at hR hR' ⊢
        simp [hR, hR', hNe', hEq]
      · simp only [Replaced] at hR ⊢
        simp [hR, hEq]

theorem TranslationInv.foldlM {ctx₀ ctx ctx' : WfIRContext OpCode}
    {done rest : List OperationPtr} {newBranch}
    (hInv : TranslationInv ctx₀ ctx done newBranch)
    (restIn : ∀ o ∈ rest, o.InBounds ctx₀.raw) (hNodup : rest.Nodup)
    (hDisjoint : ∀ o ∈ rest, o ∉ done)
    (h : rest.foldlM convertLLVMBranch ctx = .ok ctx') :
    ∃ done' newBranch', TranslationInv ctx₀ ctx' done' newBranch' ∧
      ∀ o, o ∈ done' ↔ o ∈ rest ∨ o ∈ done := by
  induction rest generalizing ctx done newBranch with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨done, newBranch, hInv, by simp⟩
  | cons op rest ih =>
    simp only [List.foldlM_cons, bind, Except.bind] at h
    split at h
    next => simp at h
    next ctx₁ hStep =>
      obtain ⟨newBranch₁, hInv₁⟩ :=
        hInv.step (restIn op (by simp)) (hDisjoint op (by simp)) hStep
      have hNodup' := List.nodup_cons.mp hNodup
      obtain ⟨done', newBranch', hInv', hMem⟩ := ih hInv₁
        (fun o ho => restIn o (by simp [ho])) hNodup'.2
        (fun o ho hMem => by
          rcases List.mem_cons.mp hMem with rfl | hMem
          · exact hNodup'.1 ho
          · exact hDisjoint o (by simp [ho]) hMem) h
      exact ⟨done', newBranch', hInv', fun o => by
        rw [hMem o]; simp only [List.mem_cons]; grind⟩

/-- The branch step computes a branch translation of its input. -/
theorem convertLLVMBranches_translation {ctx ctx' : WfIRContext OpCode}
    (h : convertLLVMBranches ctx = .ok ctx') : Nonempty (LLVMBranchTranslation ctx ctx') := by
  have hKeys : ∀ o : OperationPtr, o ∈ ctx.raw.operations.keys ↔ o.InBounds ctx.raw := fun o => by
    rw [Std.HashMap.mem_keys, OperationPtr.inBounds_def]
  have hNodup : ctx.raw.operations.keys.Nodup := by
    have := ctx.raw.operations.distinct_keys
    simpa [List.Nodup] using this
  obtain ⟨done, newBranch, hInv, hDone⟩ :=
    (TranslationInv.init (newBranch := fun _ => default)).foldlM (fun o ho => (hKeys o).mp ho)
      hNodup (fun _ _ h => by simp at h) h
  have hReplaced : ∀ o, o.InBounds ctx.raw → (Replaced ctx.raw done o ↔ o.IsLLVMBranch ctx.raw) :=
    fun o oIn => ⟨fun h => h.2, fun hB => ⟨(hDone o).mpr (.inl ((hKeys o).mpr oIn)), hB⟩⟩
  refine ⟨{
    newBranch := newBranch
    ctxSame := hInv.ctxSame
    types := hInv.types
    opSame := fun opIn hBranch => hInv.ops _ opIn fun hR => hBranch hR.2
    opList := fun {block} blockIn => ?_
    newBranchSpec := fun opIn hBranch => ?_
    newBr := fun opIn hType =>
      (hInv.branch _ ((hReplaced _ opIn).mpr (.inl hType))).newBr hType
    newBrCond := fun opIn hType =>
      (hInv.branch _ ((hReplaced _ opIn).mpr (.inr hType))).newBrCond hType }⟩
  · rw [hInv.opList block blockIn]
    refine List.map_congr_left fun o hMem => ?_
    have oIn : o.InBounds ctx.raw := by
      simp only [BlockPtr.opList] at hMem
      grind [BlockPtr.operationListWF, BlockPtr.OpChain]
    simp only [hReplaced o oIn, translateOp]
  · have hB := hInv.branch _ ((hReplaced _ opIn).mpr hBranch)
    exact ⟨hB.newIn, hB.newResultTypes, hB.newOperands, hB.newSuccessors⟩

/-! ## The branch step refines the module -/

/--
  The branch step of `llvm-to-gmir` refines in CTrees, without assuming anything
  about the interpreter, a module whose opcodes are proved monotone in CTrees
  (`OpCode.treeMonotoneProved`). The operations the step keeps see refined
  values, since the functions of the result are called with refined arguments.
-/
theorem convertLLVMBranches_isModuleRefinedByCTree_of_treeMonotoneProved
    {ctx ctx' : WfIRContext OpCode} (h : convertLLVMBranches ctx = .ok ctx')
    (hMonotone : ∀ o : OperationPtr, o.InBounds ctx.raw → (o.getOpType! ctx.raw).treeMonotoneProved)
    (module : OperationPtr) : module.isModuleRefinedByCTree ctx module ctx' := by
  obtain ⟨T⟩ := convertLLVMBranches_translation h
  exact T.isModuleRefinedByCTree
    (T.keptOpsSim_of_provedMonotoneOps (provedMonotoneOps_of_treeMonotoneProved hMonotone)) module

/--
  The branch step of `llvm-to-gmir` refines a module that verifies, in CTrees. The
  operations it keeps must be monotone in CTrees: those whose opcode has a proof
  are, and the others by `OpCode.interpretCTree_monotone_assumed`.
-/
theorem convertLLVMBranches_isModuleRefinedByCTree {ctx ctx' : WfIRContext OpCode}
    {root : OperationPtr} (hVerified : ctx.Verified root)
    (h : convertLLVMBranches ctx = .ok ctx') (module : OperationPtr) :
    module.isModuleRefinedByCTree ctx module ctx' := by
  obtain ⟨T⟩ := convertLLVMBranches_translation h
  exact T.isModuleRefinedByCTree
    (T.keptOpsSim_of_treeMonotoneOps (treeMonotoneOps_of_verified hVerified)) module

end Veir

/-!
## Axioms of the refinement theorems

Pinned so that a change to the axioms the proofs rest on shows up here. The
theorems rest on the axioms of `CTree.Sim`, but not on `CTree.Sim.trans_rel`: the
simulation relates refined states directly. The theorem for a module that verifies
assumes that the opcodes without a proof are monotone in CTrees
(`OpCode.interpretCTree_monotone_assumed`); the one for opcodes proved monotone
assumes nothing about the interpreter.
-/

/--
info: 'Veir.LLVMBranchTranslation.isModuleRefinedByCTree' depends on axioms: [propext,
 CTree.Sim,
 Classical.choice,
 Quot.sound,
 CTree.Sim.bind,
 CTree.Sim.interp,
 CTree.Sim.iter,
 CTree.Sim.ret,
 CTree.Sim.tau_l,
 CTree.Sim.tau_r,
 CTree.Sim.ub]
-/
#guard_msgs in
#print axioms Veir.LLVMBranchTranslation.isModuleRefinedByCTree

/--
info: 'Veir.convertLLVMBranches_translation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Veir.convertLLVMBranches_translation

/--
info: 'Veir.convertLLVMBranches_isModuleRefinedByCTree_of_treeMonotoneProved' depends on axioms: [propext,
 CTree.Sim,
 Classical.choice,
 Quot.sound,
 CTree.Sim.bind,
 CTree.Sim.interp,
 CTree.Sim.iter,
 CTree.Sim.ret,
 CTree.Sim.tau_l,
 CTree.Sim.tau_r,
 CTree.Sim.ub]
-/
#guard_msgs in
#print axioms Veir.convertLLVMBranches_isModuleRefinedByCTree_of_treeMonotoneProved

/--
info: 'Veir.convertLLVMBranches_isModuleRefinedByCTree' depends on axioms: [propext,
 CTree.Sim,
 Classical.choice,
 Quot.sound,
 CTree.Sim.bind,
 CTree.Sim.interp,
 CTree.Sim.iter,
 CTree.Sim.ret,
 CTree.Sim.tau_l,
 CTree.Sim.tau_r,
 CTree.Sim.ub,
 Veir.OpCode.interpretCTree_monotone_assumed]
-/
#guard_msgs in
#print axioms Veir.convertLLVMBranches_isModuleRefinedByCTree
