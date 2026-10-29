module

public import Veir.Passes.InstructionSelection.Branches.Frame
public import Veir.Passes.InstructionSelection.Branches.Simulation

import all Veir.Passes.InstructionSelection.RISCV64Branches
public import Veir.Passes.Matching.GMIR.Basic
import all Veir.Passes.Matching.GMIR.Basic
import all Veir.IR.Basic
import all Veir.IR.OpCode

public section

/-!
# The pass computes a branch lowering

`convertModule` succeeds only with a module that is the `BranchLowering` of its
input, if the input verifies, so the module it returns refines the one it was
given.
-/

namespace Veir

theorem castToReg_ok {ip : InsertPoint} {ctx ctx' : WfIRContext OpCode}
    {casts casts' : Array OperationPtr} {operand : ValuePtr}
    (h : castToReg ip (ctx, casts) operand = .ok (ctx', casts')) :
    ∃ cast, casts' = casts.push cast ∧
      WfRewriter.createOp! ctx Builtin.unrealized_conversion_cast #[RegisterType.mk] #[operand] #[]
        #[] default (some ip) = some (ctx', cast) := by
  simp only [castToReg] at h
  split at h
  next ctx₁ cast hCreate =>
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨cast, rfl, hCreate⟩
  next => simp [throw, throwThe, MonadExceptOf.throw] at h

/-- `regOf` creates the cast of a value to a register, or the read of `x0`, in front of `ip`. -/
theorem regOf_ok {ip : InsertPoint} {ctx ctx' : WfIRContext OpCode} {regs regs' : Array ValuePtr}
    {source : Option ValuePtr} (h : regOf ip (ctx, regs) source = .ok (ctx', regs')) :
    ∃ newOp, regs' = regs.push (newOp.getResult 0) ∧
      match source with
      | some value => WfRewriter.createOp! ctx Builtin.unrealized_conversion_cast
          #[RegisterType.mk] #[value] #[] #[] default (some ip) = some (ctx', newOp)
      | none => WfRewriter.createOp! ctx Rv64.get_register
          #[(RegisterType.mk (some 0) : TypeAttr)] #[] #[] #[] () (some ip) = some (ctx', newOp) := by
  rcases source with _ | value
  · simp only [regOf] at h
    split at h
    next ctx₁ x0 hCreate =>
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨x0, rfl, hCreate⟩
    next => simp [throw, throwThe, MonadExceptOf.throw] at h
  · simp only [regOf, bind, Except.bind] at h
    split at h
    next => simp at h
    next acc hCast =>
      obtain ⟨ctx₁, casts⟩ := acc
      obtain ⟨cast, rfl, hCreate⟩ := castToReg_ok hCast
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨cast, by simp, hCreate⟩

/-- `newOp` puts `source` into a register: it casts a value to one, or reads `x0`. -/
@[expose]
def RegOpIs (ctx : IRContext OpCode) (newOp : OperationPtr) : Option ValuePtr → Prop
  | some value => newOp.getOpType! ctx = .builtin .unrealized_conversion_cast ∧
      newOp.getResultTypes! ctx = #[(RegisterType.mk : TypeAttr)] ∧
      newOp.getOperands! ctx = #[value]
  | none => newOp.getOpType! ctx = .rv64 .get_register ∧
      newOp.getResultTypes! ctx = #[(RegisterType.mk (some 0) : TypeAttr)] ∧
      newOp.getOperands! ctx = #[]

/-- An operation that stays the same keeps putting its source into a register. -/
theorem RegOpIs.of_opSame {f : ValuePtr → ValuePtr} {ctx ctx' : IRContext OpCode}
    {newOp : OperationPtr} {source : Option ValuePtr} (hSame : OpSame f ctx ctx' newOp)
    (h : RegOpIs ctx newOp source) : RegOpIs ctx' newOp (source.map f) := by
  rcases source with _ | value <;> simp only [RegOpIs, Option.map] at h ⊢ <;>
    obtain ⟨h₁, h₂, h₃⟩ := h
  · exact ⟨hSame.opType.trans h₁, hSame.resultTypes.trans h₂, by rw [hSame.operands, h₃]; simp⟩
  · exact ⟨hSame.opType.trans h₁, hSame.resultTypes.trans h₂, by rw [hSame.operands, h₃]; simp⟩

/-! ## Putting the operands of a branch into registers -/

/--
  The module while the registers in front of the branch `op` are made: `regOps`
  put `sources` into registers, in front of `op`, and nothing else changed since
  `ctx₀`.
-/
structure RegsInv (ctx₀ : WfIRContext OpCode) (op : OperationPtr) (sources : List (Option ValuePtr))
    (ctx : WfIRContext OpCode) (regOps : Array OperationPtr) : Prop where
  ops : ∀ o, o.InBounds ctx₀.raw → OpSame id ctx₀.raw ctx.raw o
  ctxSame : CtxSame ctx₀.raw ctx.raw
  types : ∀ value : ValuePtr, value.InBounds ctx₀.raw →
    value.InBounds ctx.raw ∧ value.getType! ctx.raw = value.getType! ctx₀.raw
  size : regOps.size = sources.length
  regOp : ∀ i (hi : i < regOps.size) (hi' : i < sources.length),
    regOps[i].InBounds ctx.raw ∧ ¬ regOps[i].InBounds ctx₀.raw ∧
    RegOpIs ctx.raw regOps[i] sources[i]
  nodup : regOps.toList.Nodup
  opList : ∀ (block : BlockPtr) (blockIn : block.InBounds ctx₀.raw),
    block.opList ctx (ctxSame.blockIn blockIn) =
      (block.opList ctx₀ blockIn).replaceBy op (regOps.toList ++ [op])

theorem RegsInv.step {ctx₀ ctx ctx' : WfIRContext OpCode} {op : OperationPtr}
    {sources : List (Option ValuePtr)} {regOps : Array OperationPtr} {regs' : Array ValuePtr}
    {source : Option ValuePtr}
    (hInv : RegsInv ctx₀ op sources ctx regOps) (opIn : op.InBounds ctx₀.raw)
    (h : regOf (.before op) (ctx, regOps.map (fun o => (o.getResult 0 : ValuePtr))) source =
      .ok (ctx', regs')) :
    ∃ newOp, regs' = (regOps.push newOp).map (fun o => (o.getResult 0 : ValuePtr)) ∧
      RegsInv ctx₀ op (sources ++ [source]) ctx' (regOps.push newOp) := by
  obtain ⟨newOp, rfl, hCreate⟩ := regOf_ok h
  /- Both shapes of the new operation share the frame of `createOp`. -/
  obtain ⟨hNotIn, hIn, hOps, hCtx, hTypes, hRegOp, hMono, hList⟩ :
      ¬ newOp.InBounds ctx.raw ∧ newOp.InBounds ctx'.raw ∧
      (∀ op, op.InBounds ctx.raw → OpSame id ctx.raw ctx'.raw op) ∧
      CtxSame ctx.raw ctx'.raw ∧
      (∀ value : ValuePtr, value.InBounds ctx.raw →
        value.getType! ctx'.raw = value.getType! ctx.raw) ∧
      RegOpIs ctx'.raw newOp source ∧
      (∀ ptr : GenericPtr, ptr.InBounds ctx.raw → ptr.InBounds ctx'.raw) ∧
      (∀ (block : BlockPtr) (blockIn : block.InBounds ctx.raw) (blockIn' : block.InBounds ctx'.raw),
        block.opList ctx' blockIn' = (block.opList ctx blockIn).replaceBy op [newOp, op]) := by
    rcases source with _ | value <;> simp only at hCreate
    · obtain ⟨h₁, h₂, h₃, h₄, hCreate⟩ := WfRewriter.createOp_of_createOp! hCreate
      obtain ⟨hNotIn, hIn, hOps, hCtx, hTypes, hType, hResultTypes, hOperands, _⟩ :=
        WfRewriter.createOp_frame hCreate
      exact ⟨hNotIn, hIn, hOps, hCtx, hTypes, ⟨hType.trans ofDialect_get_register, hResultTypes,
        hOperands⟩, fun ptr => WfRewriter.createOp_inBounds_mono hCreate,
        fun block blockIn blockIn' => WfRewriter.createOp_before_opList hCreate blockIn blockIn'⟩
    · obtain ⟨h₁, h₂, h₃, h₄, hCreate⟩ := WfRewriter.createOp_of_createOp! hCreate
      obtain ⟨hNotIn, hIn, hOps, hCtx, hTypes, hType, hResultTypes, hOperands, _⟩ :=
        WfRewriter.createOp_frame hCreate
      exact ⟨hNotIn, hIn, hOps, hCtx, hTypes, ⟨hType.trans ofDialect_cast, hResultTypes,
        hOperands⟩, fun ptr => WfRewriter.createOp_inBounds_mono hCreate,
        fun block blockIn blockIn' => WfRewriter.createOp_before_opList hCreate blockIn blockIn'⟩
  have hOld : ∀ i (hi : i < regOps.size), regOps[i] ≠ newOp := fun i hi hEq =>
    hNotIn (hEq ▸ (hInv.regOp i hi (by rw [← hInv.size]; exact hi)).1)
  refine ⟨newOp, by simp, fun o oIn => (hInv.ops o oIn).trans_id (hOps o (hInv.ops o oIn).inBounds),
    hInv.ctxSame.trans hCtx, fun v vIn => ?_, by simp [hInv.size], fun i hi hi' => ?_, ?_,
    fun block blockIn => ?_⟩
  · have := hInv.types v vIn
    exact ⟨by simpa using hMono (.value v) (by simpa using this.1),
      (hTypes v this.1).trans this.2⟩
  · by_cases hLt : i < regOps.size
    · obtain ⟨c₁, c₂, c₃⟩ := hInv.regOp i hLt (by rw [← hInv.size]; exact hLt)
      have hSame := hOps regOps[i] c₁
      simp only [Array.getElem_push_lt hLt, List.getElem_append_left (hInv.size ▸ hLt)]
      exact ⟨hSame.inBounds, c₂, by simpa using c₃.of_opSame hSame⟩
    · have hEq : i = regOps.size := by simp at hi; omega
      subst hEq
      have hNotIn₀ : ¬ newOp.InBounds ctx₀.raw := fun h => hNotIn (hInv.ops newOp h).inBounds
      simp only [Array.getElem_push_eq]
      simp only [hInv.size, List.getElem_concat_length]
      exact ⟨hIn, hNotIn₀, hRegOp⟩
  · rw [Array.toList_push, List.nodup_append]
    refine ⟨hInv.nodup, by simp, fun a ha b hb => ?_⟩
    obtain rfl : b = newOp := by simpa using hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    exact hOld i (by simpa using hi)
  · have hNotMem : op ∉ regOps.toList := fun hMem => by
      obtain ⟨i, hi, hEq⟩ := List.getElem_of_mem hMem
      have hi' : i < regOps.size := by simpa using hi
      have hEq' : regOps[i] = op := by simpa using hEq
      exact (hInv.regOp i hi' (by rw [← hInv.size]; exact hi')).2.1 (hEq' ▸ opIn)
    rw [hList block (hInv.ctxSame.blockIn blockIn), hInv.opList block blockIn,
      List.replaceBy_replaceBy hNotMem]
    simp

theorem RegsInv.foldlM {ctx₀ ctx ctx' : WfIRContext OpCode} {op : OperationPtr}
    {sources rest : List (Option ValuePtr)} {regOps : Array OperationPtr} {regs' : Array ValuePtr}
    (hInv : RegsInv ctx₀ op sources ctx regOps) (opIn : op.InBounds ctx₀.raw)
    (h : rest.foldlM (regOf (.before op)) (ctx, regOps.map (fun o => (o.getResult 0 : ValuePtr))) =
      .ok (ctx', regs')) :
    ∃ regOps', regs' = regOps'.map (fun o => (o.getResult 0 : ValuePtr)) ∧
      RegsInv ctx₀ op (sources ++ rest) ctx' regOps' := by
  induction rest generalizing sources ctx regOps with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨regOps, rfl, by simpa using hInv⟩
  | cons source rest ih =>
    simp only [List.foldlM_cons, bind, Except.bind] at h
    split at h
    next => simp at h
    next acc hStep =>
      obtain ⟨ctx₁, regs₁⟩ := acc
      obtain ⟨newOp, rfl, hInv₁⟩ := hInv.step opIn hStep
      obtain ⟨regOps', rfl, hInv'⟩ := ih hInv₁ h
      exact ⟨regOps', rfl, by simpa using hInv'⟩

theorem RegsInv.init {ctx₀ : WfIRContext OpCode} {op : OperationPtr} :
    RegsInv ctx₀ op [] ctx₀ #[] :=
  ⟨fun _ oIn => OpSame.refl oIn, CtxSame.refl, fun _ vIn => ⟨vIn, rfl⟩, rfl,
    fun _ hi => by simp at hi, by simp, fun block blockIn => by
      simp [List.replaceBy_self]⟩

/-- `regOperands` reads only the operands of the branch. -/
theorem regOperands_congr {ctx ctx' : IRContext OpCode} {op : OperationPtr}
    {compare : Option Compare} (h : op.getOperands! ctx' = op.getOperands! ctx) :
    regOperands ctx' op compare = regOperands ctx op compare := by
  have hNum : op.getNumOperands! ctx' = op.getNumOperands! ctx := by
    rw [← OperationPtr.getOperands!.size_eq_getNumOperands!, h,
      OperationPtr.getOperands!.size_eq_getNumOperands!]
  have hOperand : ∀ i, op.getOperand! ctx' i = op.getOperand! ctx i := by
    intro i
    rw [← OperationPtr.getOperands!.getElem!_eq_getOperand!, h,
      OperationPtr.getOperands!.getElem!_eq_getOperand!]
  simp only [regOperands, hNum, hOperand]

/-! ## Lowering one branch -/

/-- The properties of the compare-and-branch that replaces a `g_brcond` with `segments`. -/
@[expose]
def compareProperties (branch : CondBranch) (segments : DenseArrayAttr) :
    propertiesOf (OpCode.riscv_cf branch.val) :=
  cast branch.property.symm
    (⟨{ segments with values := #[1] ++ segments.values }⟩ : RISCVBrProperties)

/--
  What lowering the branch `op` does: `regOps` put the values `regOperands` names
  into registers, and they and `newBranch` take the place of `op`.
-/
structure BranchStep (ctx ctx' : WfIRContext OpCode) (op : OperationPtr)
    (compare : Option Compare) (regOps : Array OperationPtr) (newBranch : OperationPtr) : Prop where
  ops : ∀ o, o.InBounds ctx.raw → o ≠ op → OpSame id ctx.raw ctx'.raw o
  ctxSame : CtxSame ctx.raw ctx'.raw
  types : ∀ value : ValuePtr, value.InBounds ctx.raw → (∀ r, value = .opResult r → r.op ≠ op) →
    value.InBounds ctx'.raw ∧ value.getType! ctx'.raw = value.getType! ctx.raw
  size : regOps.size = (regOperands ctx.raw op compare).length
  regOp : ∀ i (hi : i < regOps.size) (hi' : i < (regOperands ctx.raw op compare).length),
    regOps[i].InBounds ctx'.raw ∧ ¬ regOps[i].InBounds ctx.raw ∧
    RegOpIs ctx'.raw regOps[i] (regOperands ctx.raw op compare)[i]
  nodup : regOps.toList.Nodup
  newIn : newBranch.InBounds ctx'.raw
  newNotIn : ¬ newBranch.InBounds ctx.raw
  newNotReg : newBranch ∉ regOps.toList
  newResultTypes : newBranch.getResultTypes! ctx'.raw = #[]
  newSuccessors : newBranch.getSuccessors! ctx'.raw = op.getSuccessors! ctx.raw
  newOperands : newBranch.getOperands! ctx'.raw =
    regOps.map (fun o => (o.getResult 0 : ValuePtr))
  newBr : op.getOpType! ctx.raw = .gmir .g_br → newBranch.getOpType! ctx'.raw = .riscv_cf .branch
  newBnez : op.getOpType! ctx.raw ≠ .gmir .g_br → compare = none →
    newBranch.getOpType! ctx'.raw = .riscv_cf .bnez ∧
    (newBranch.getProperties! ctx'.raw (OpCode.riscv_cf .bnez)).operandSegmentSizes =
      (op.getProperties! ctx.raw (OpCode.gmir .g_brcond)).operandSegmentSizes
  newCompare : op.getOpType! ctx.raw ≠ .gmir .g_br → ∀ branch l r,
    compare = some (branch, l, r) →
    newBranch.getOpType! ctx'.raw = .riscv_cf branch.val ∧
    newBranch.getProperties! ctx'.raw (OpCode.riscv_cf branch.val) = compareProperties branch
      (op.getProperties! ctx.raw (OpCode.gmir .g_brcond)).operandSegmentSizes
  opList : ∀ (block : BlockPtr) (blockIn : block.InBounds ctx.raw),
    block.opList ctx' (ctxSame.blockIn blockIn) =
      (block.opList ctx blockIn).replaceBy op (regOps.toList ++ [newBranch])

/-- The branch step from the registers, the creation of the new branch, and the erasure. -/
theorem BranchStep.of_frames {ctx ctx₁ ctx₂ ctx' : WfIRContext OpCode} {op newBranch : OperationPtr}
    {compare : Option Compare} {regOps : Array OperationPtr} (opIn : op.InBounds ctx.raw)
    (hInv : RegsInv ctx op (regOperands ctx.raw op compare) ctx₁ regOps)
    (hNotIn : ¬ newBranch.InBounds ctx₁.raw) (hIn : newBranch.InBounds ctx₂.raw)
    (hOps : ∀ o, o.InBounds ctx₁.raw → OpSame id ctx₁.raw ctx₂.raw o)
    (hCtx : CtxSame ctx₁.raw ctx₂.raw)
    (hTypes : ∀ value : ValuePtr, value.InBounds ctx₁.raw →
      value.getType! ctx₂.raw = value.getType! ctx₁.raw)
    (hMono : ∀ ptr : GenericPtr, ptr.InBounds ctx₁.raw → ptr.InBounds ctx₂.raw)
    (hResultTypes : newBranch.getResultTypes! ctx₂.raw = #[])
    (hSuccessors : newBranch.getSuccessors! ctx₂.raw = op.getSuccessors! ctx.raw)
    (hOperands : newBranch.getOperands! ctx₂.raw =
      regOps.map (fun o => (o.getResult 0 : ValuePtr)))
    (hBr : op.getOpType! ctx.raw = .gmir .g_br →
      newBranch.getOpType! ctx₂.raw = .riscv_cf .branch)
    (hBnez : op.getOpType! ctx.raw ≠ .gmir .g_br → compare = none →
      newBranch.getOpType! ctx₂.raw = .riscv_cf .bnez ∧
      (newBranch.getProperties! ctx₂.raw (OpCode.riscv_cf .bnez)).operandSegmentSizes =
        (op.getProperties! ctx.raw (OpCode.gmir .g_brcond)).operandSegmentSizes)
    (hCompare : op.getOpType! ctx.raw ≠ .gmir .g_br → ∀ branch l r,
      compare = some (branch, l, r) →
      newBranch.getOpType! ctx₂.raw = .riscv_cf branch.val ∧
      newBranch.getProperties! ctx₂.raw (OpCode.riscv_cf branch.val) = compareProperties branch
        (op.getProperties! ctx.raw (OpCode.gmir .g_brcond)).operandSegmentSizes)
    (hList : ∀ (block : BlockPtr) (blockIn : block.InBounds ctx₁.raw)
      (blockIn' : block.InBounds ctx₂.raw),
      block.opList ctx₂ blockIn' = (block.opList ctx₁ blockIn).replaceBy op [newBranch, op])
    (hResults₀ : op.getNumResults! ctx.raw = 0) (hRegions₀ : op.getNumRegions! ctx.raw = 0)
    (hErase : ctx' = WfRewriter.eraseOp! ctx₂ op) :
    BranchStep ctx ctx' op compare regOps newBranch := by
  subst hErase
  have opIn₂ : op.InBounds ctx₂.raw := (hOps op (hInv.ops op opIn).inBounds).inBounds
  have hSameOp : OpSame id ctx.raw ctx₂.raw op :=
    (hInv.ops op opIn).trans_id (hOps op (hInv.ops op opIn).inBounds)
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
  have hNewNe : newBranch ≠ op := fun hEq => hNotIn (hEq ▸ (hInv.ops op opIn).inBounds)
  have hNewSame := hOps₃ newBranch hIn hNewNe
  have hRegNotOp : op ∉ regOps.toList := fun hMem => by
    obtain ⟨i, hi, hEq⟩ := List.getElem_of_mem hMem
    have hi' : i < regOps.size := by simpa using hi
    have hEq' : regOps[i] = op := by simpa using hEq
    exact (hInv.regOp i hi' (by simpa [hInv.size] using hi')).2.1 (hEq' ▸ opIn)
  refine {
    ops := fun o oIn hNe =>
      ((hInv.ops o oIn).trans_id (hOps o (hInv.ops o oIn).inBounds)).trans_id
        (hOps₃ o (hOps o (hInv.ops o oIn).inBounds).inBounds hNe)
    ctxSame := (hInv.ctxSame.trans hCtx).trans hCtx₃
    types := fun v vIn hv => ?_
    size := hInv.size
    regOp := fun i hi hi' => ?_
    nodup := hInv.nodup
    newIn := hNewSame.inBounds
    newNotIn := fun h => hNotIn (hInv.ops newBranch h).inBounds
    newNotReg := fun hMem => ?_
    newResultTypes := hNewSame.resultTypes.trans hResultTypes
    newSuccessors := hNewSame.successors.trans hSuccessors
    newOperands := by rw [hNewSame.operands, hOperands]; simp
    newBr := fun h => hNewSame.opType.trans (hBr h)
    newBnez := fun h hc => ⟨hNewSame.opType.trans (hBnez h hc).1,
      by rw [hNewSame.properties]; exact (hBnez h hc).2⟩
    newCompare := fun h branch l r hc => ⟨hNewSame.opType.trans (hCompare h branch l r hc).1,
      by rw [hNewSame.properties]; exact (hCompare h branch l r hc).2⟩
    opList := fun block blockIn => ?_ }
  · have h₁ := hInv.types v vIn
    have h₂ : v.InBounds ctx₂.raw := by simpa using hMono (.value v) (by simpa using h₁.1)
    have h₃ := hValues₃ v h₂ hv
    exact ⟨h₃, (hTypes₃ v h₃).trans ((hTypes v h₁.1).trans h₁.2)⟩
  · obtain ⟨c₁, c₂, c₃⟩ := hInv.regOp i hi hi'
    have hNe : regOps[i] ≠ op := fun hEq => c₂ (hEq ▸ opIn)
    have hSame := (hOps regOps[i] c₁).trans_id (hOps₃ regOps[i] (hOps regOps[i] c₁).inBounds hNe)
    exact ⟨hSame.inBounds, c₂, by simpa using c₃.of_opSame hSame⟩
  · obtain ⟨i, hi, hEq⟩ := List.getElem_of_mem hMem
    have hi' : i < regOps.size := by simpa using hi
    have hEq' : regOps[i] = newBranch := by simpa using hEq
    exact hNotIn (hEq' ▸ (hInv.regOp i hi' (by simpa [hInv.size] using hi')).1)
  · have blockIn₁ := hInv.ctxSame.blockIn blockIn
    have blockIn₂ := hCtx.blockIn blockIn₁
    rw [WfRewriter.eraseOp_opList blockIn₂, hList block blockIn₁ blockIn₂,
      hInv.opList block blockIn, List.replaceBy_replaceBy hRegNotOp,
      show regOps.toList ++ [newBranch, op] = (regOps.toList ++ [newBranch]) ++ [op] by simp,
      List.erase_replaceBy BlockPtr.opList_nodup]
    simp only [List.mem_append, List.mem_singleton, not_or]
    exact ⟨hRegNotOp, fun hEq => hNewNe hEq.symm⟩

/--
  What `convertBranch` leaves behind, for an operation that is not an
  `llvm.unreachable`. The lowering replaces that one too, which this proof does
  not cover; `convertModule_branchLowering` assumes the module has none.
-/
theorem convertBranch_ok {convertible : BlockPtr → Bool}
    {compareOf : OperationPtr → Option Compare} {ctx ctx' : WfIRContext OpCode} {op : OperationPtr}
    (opIn : op.InBounds ctx.raw)
    (hNotUnreachable : op.getOpType! ctx.raw ≠ OpCode.llvm .unreachable)
    (hCounts : op.IsGmirBranch ctx.raw →
      op.getNumResults! ctx.raw = 0 ∧ op.getNumRegions! ctx.raw = 0)
    (h : convertBranch convertible compareOf ctx op = .ok ctx') :
    (¬ op.IsGmirBranch ctx.raw ∧ ctx' = ctx) ∨
    (op.IsGmirBranch ctx.raw ∧ ¬ (op.getSuccessors! ctx.raw).all convertible ∧ ctx' = ctx) ∨
    (op.IsGmirBranch ctx.raw ∧
      ∃ regOps newBranch, BranchStep ctx ctx' op (compareOf op) regOps newBranch) := by
  simp only [convertBranch, bind, Except.bind] at h
  simp only [hNotUnreachable, ↓reduceIte] at h
  split at h
  next hBranch =>
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact .inl ⟨hBranch, h.symm⟩
  next hBranch =>
    split at h
    next hGate =>
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact .inr (.inl ⟨by simpa using hBranch, by simpa using hGate, h.symm⟩)
    next =>
      have hC := hCounts (by simpa using hBranch)
      refine .inr (.inr ⟨by simpa using hBranch, ?_⟩)
      split at h
      next => simp at h
      next acc hFold =>
        obtain ⟨ctx₁, regs⟩ := acc
        obtain ⟨regOps, rfl, hInv⟩ := (RegsInv.init (ctx₀ := ctx) (op := op)).foldlM opIn
          (rest := regOperands ctx.raw op (compareOf op)) (by simpa using hFold)
        simp only [List.nil_append] at hInv
        split at h
        next hType =>
          split at h
          next ctx₂ newBranch hCreate =>
            refine ⟨regOps, newBranch, ?_⟩
            obtain ⟨h₁, h₂, h₃, h₄, hCreate⟩ := WfRewriter.createOp_of_createOp! hCreate
            obtain ⟨hNotIn, hIn, hOps, hCtx, hTypes, hNewType, hResultTypes, hOperands,
              hSuccessors⟩ := WfRewriter.createOp_frame hCreate
            exact BranchStep.of_frames opIn hInv hNotIn hIn hOps hCtx hTypes
              (fun ptr => WfRewriter.createOp_inBounds_mono hCreate) hResultTypes hSuccessors
              hOperands (fun _ => hNewType.trans (ofDialect_riscv_cf _))
              (fun hNe => absurd hType hNe) (fun hNe => absurd hType hNe)
              (fun block blockIn blockIn' =>
                WfRewriter.createOp_before_opList hCreate blockIn blockIn')
              hC.1 hC.2 (by simpa [pure, Except.pure] using h.symm)
          next => simp at h
        next hType =>
          generalize hCmp : compareOf op = compare at h hInv ⊢
          split at h
          next ctx₂ newBranch hCreate =>
            refine ⟨regOps, newBranch, ?_⟩
            obtain ⟨h₁, h₂, h₃, h₄, hCreate⟩ := WfRewriter.createOp_of_createOp! hCreate
            have hProps := WfRewriter.createOp_riscv_cf_properties hCreate
            obtain ⟨hNotIn, hIn, hOps, hCtx, hTypes, hNewType, hResultTypes, hOperands,
              hSuccessors⟩ := WfRewriter.createOp_frame hCreate
            refine BranchStep.of_frames opIn hInv hNotIn hIn hOps hCtx hTypes
              (fun ptr => WfRewriter.createOp_inBounds_mono hCreate) hResultTypes hSuccessors
              hOperands (fun h => absurd h hType) (fun _ hc => ?_) (fun _ branch l r hc => ?_)
              (fun block blockIn blockIn' =>
                WfRewriter.createOp_before_opList hCreate blockIn blockIn')
              hC.1 hC.2 (by simpa [pure, Except.pure] using h.symm)
            · subst hc
              exact ⟨hNewType.trans (ofDialect_riscv_cf _), by rw [hProps]; rfl⟩
            · subst hc
              exact ⟨hNewType.trans (ofDialect_riscv_cf _), by rw [hProps]; rfl⟩
          next => simp at h

/-! ## Lowering all branches -/

/-- What the lowering of the branch `op` of `ctx₀` left in `ctx`. -/
structure LoweredBranch (ctx₀ ctx : WfIRContext OpCode) (op : OperationPtr)
    (compare : Option Compare) (regOp : Nat → OperationPtr) (newBranch : OperationPtr) : Prop where
  numResults : op.getNumResults! ctx₀.raw = 0
  regOpSpec : ∀ i, i < (regOperands ctx₀.raw op compare).length →
    (regOp i).InBounds ctx.raw ∧
    (∀ result : OpResultPtr, result.InBounds ctx₀.raw → result.op ≠ regOp i) ∧
    RegOpIs ctx.raw (regOp i) (regOperands ctx₀.raw op compare)[i]?.join
  regOpInj : ∀ i j, i < (regOperands ctx₀.raw op compare).length →
    j < (regOperands ctx₀.raw op compare).length → regOp i = regOp j → i = j
  newIn : newBranch.InBounds ctx.raw
  newResultTypes : newBranch.getResultTypes! ctx.raw = #[]
  newSuccessors : newBranch.getSuccessors! ctx.raw = op.getSuccessors! ctx₀.raw
  newOperands : newBranch.getOperands! ctx.raw =
    (Array.range (regOperands ctx₀.raw op compare).length).map
      (fun i => ((regOp i).getResult 0 : ValuePtr))
  newBr : op.getOpType! ctx₀.raw = .gmir .g_br → newBranch.getOpType! ctx.raw = .riscv_cf .branch
  newBnez : op.getOpType! ctx₀.raw = .gmir .g_brcond → compare = none →
    newBranch.getOpType! ctx.raw = .riscv_cf .bnez ∧
    (newBranch.getProperties! ctx.raw (OpCode.riscv_cf .bnez)).operandSegmentSizes =
      (op.getProperties! ctx₀.raw (OpCode.gmir .g_brcond)).operandSegmentSizes
  newCompare : op.getOpType! ctx₀.raw = .gmir .g_brcond → ∀ branch l r,
    compare = some (branch, l, r) →
    newBranch.getOpType! ctx.raw = .riscv_cf branch.val ∧
    newBranch.getProperties! ctx.raw (OpCode.riscv_cf branch.val) = compareProperties branch
      (op.getProperties! ctx₀.raw (OpCode.gmir .g_brcond)).operandSegmentSizes

/-- The new operations of a lowered branch are not gMIR branches. -/
theorem LoweredBranch.not_isGmirBranch {ctx₀ ctx : WfIRContext OpCode} {o : OperationPtr}
    {compare : Option Compare} {regOp : Nat → OperationPtr} {newBranch : OperationPtr}
    (h : LoweredBranch ctx₀ ctx o compare regOp newBranch) (hBranch : o.IsGmirBranch ctx₀.raw) :
    ¬ newBranch.IsGmirBranch ctx.raw ∧
    ∀ i, i < (regOperands ctx₀.raw o compare).length → ¬ (regOp i).IsGmirBranch ctx.raw := by
  refine ⟨fun hNew => ?_, fun i hi hReg => ?_⟩
  · rcases hBranch with hB | hB
    · rcases hNew with h' | h' <;> simp [h.newBr hB] at h'
    · rcases hc : compare with _ | ⟨branch, l, r⟩
      · rcases hNew with h' | h' <;> simp [(h.newBnez hB hc).1] at h'
      · rcases hNew with h' | h' <;> simp [(h.newCompare hB branch l r hc).1] at h'
  · have hSpec := (h.regOpSpec i hi).2.2
    rcases hs : (regOperands ctx₀.raw o compare)[i]?.join with _ | value <;>
      simp only [hs, RegOpIs] at hSpec <;>
      rcases hReg with h' | h' <;> simp [hSpec.1] at h'

/-- An operation that stays the same stays a lowered branch's register or new branch. -/
theorem LoweredBranch.mono {ctx₀ ctx ctx' : WfIRContext OpCode} {o : OperationPtr}
    {compare : Option Compare} {regOp : Nat → OperationPtr} {newBranch : OperationPtr}
    (h : LoweredBranch ctx₀ ctx o compare regOp newBranch) (hBranch : o.IsGmirBranch ctx₀.raw)
    (hSame : ∀ o', o'.InBounds ctx.raw → ¬ o'.IsGmirBranch ctx.raw →
      OpSame id ctx.raw ctx'.raw o') :
    LoweredBranch ctx₀ ctx' o compare regOp newBranch := by
  have hNot := h.not_isGmirBranch hBranch
  have hNew : OpSame id ctx.raw ctx'.raw newBranch := hSame newBranch h.newIn hNot.1
  refine ⟨h.numResults, fun i hi => ?_, h.regOpInj, hNew.inBounds,
    hNew.resultTypes.trans h.newResultTypes, hNew.successors.trans h.newSuccessors,
    by rw [hNew.operands, h.newOperands]; simp, fun hB => hNew.opType.trans (h.newBr hB),
    fun hB hc => ⟨hNew.opType.trans (h.newBnez hB hc).1,
      by rw [hNew.properties]; exact (h.newBnez hB hc).2⟩,
    fun hB branch l r hc => ⟨hNew.opType.trans (h.newCompare hB branch l r hc).1,
      by rw [hNew.properties]; exact (h.newCompare hB branch l r hc).2⟩⟩
  obtain ⟨c₁, c₂, c₃⟩ := h.regOpSpec i hi
  have hS := hSame (regOp i) c₁ (hNot.2 i hi)
  exact ⟨hS.inBounds, c₂, by simpa using c₃.of_opSame hS⟩

/-- The operations that stand for the branch `o` once it is lowered. -/
@[expose]
def loweredOps (ctx₀ : IRContext OpCode) (compareOf : OperationPtr → Option Compare)
    (regOp : OperationPtr → Nat → OperationPtr) (newBranch : OperationPtr → OperationPtr)
    (o : OperationPtr) : List OperationPtr :=
  (List.range (regOperands ctx₀ o (compareOf o)).length).map (regOp o) ++ [newBranch o]

/-- The module after the branches among `done` were lowered. -/
structure PhaseA (ctx₀ ctx : WfIRContext OpCode) (done : List OperationPtr)
    (compareOf : OperationPtr → Option Compare)
    (regOp : OperationPtr → Nat → OperationPtr) (newBranch : OperationPtr → OperationPtr) :
    Prop where
  ops : ∀ o, o.InBounds ctx₀.raw → ¬ (o ∈ done ∧ o.IsGmirBranch ctx₀.raw) →
    OpSame id ctx₀.raw ctx.raw o
  ctxSame : CtxSame ctx₀.raw ctx.raw
  types : ∀ value : ValuePtr, value.InBounds ctx₀.raw →
    value.InBounds ctx.raw ∧ value.getType! ctx.raw = value.getType! ctx₀.raw
  other : ∀ o ∈ done, ¬ o.IsGmirBranch ctx₀.raw → o.getNumSuccessors! ctx₀.raw = 0
  branch : ∀ o ∈ done, o.IsGmirBranch ctx₀.raw →
    LoweredBranch ctx₀ ctx o (compareOf o) (regOp o) (newBranch o)
  opList : ∀ (block : BlockPtr) (blockIn : block.InBounds ctx₀.raw),
    block.opList ctx (ctxSame.blockIn blockIn) =
      (block.opList ctx₀ blockIn).flatMap fun o =>
        if o ∈ done ∧ o.IsGmirBranch ctx₀.raw then loweredOps ctx₀.raw compareOf regOp newBranch o
        else [o]

theorem PhaseA.init {ctx₀ : WfIRContext OpCode} {compareOf regOp newBranch} :
    PhaseA ctx₀ ctx₀ [] compareOf regOp newBranch :=
  ⟨fun _ oIn _ => OpSame.refl oIn, CtxSame.refl, fun _ vIn => ⟨vIn, rfl⟩,
    fun _ h => by simp at h, fun _ h => by simp at h, fun _ _ => by simp⟩

theorem PhaseA.step_other {ctx₀ ctx : WfIRContext OpCode} {done : List OperationPtr}
    {compareOf regOp newBranch} {op : OperationPtr}
    (hInv : PhaseA ctx₀ ctx done compareOf regOp newBranch)
    (hBranch : ¬ op.IsGmirBranch ctx₀.raw) (hSuccessors : op.getNumSuccessors! ctx₀.raw = 0) :
    PhaseA ctx₀ ctx (op :: done) compareOf regOp newBranch := by
  have hIff : ∀ o, (o ∈ op :: done ∧ o.IsGmirBranch ctx₀.raw) ↔
      (o ∈ done ∧ o.IsGmirBranch ctx₀.raw) := by
    intro o
    constructor
    · rintro ⟨hMem, hB⟩
      rcases List.mem_cons.mp hMem with rfl | hMem
      · exact absurd hB hBranch
      · exact ⟨hMem, hB⟩
    · exact fun ⟨hMem, hB⟩ => ⟨List.mem_cons_of_mem _ hMem, hB⟩
  refine ⟨fun o oIn hNot => hInv.ops o oIn (by rwa [← hIff]), hInv.ctxSame, hInv.types,
    fun o hMem hB => ?_, fun o hMem hB => hInv.branch o ((hIff o).mp ⟨hMem, hB⟩).1 hB,
    fun block blockIn => ?_⟩
  · rcases List.mem_cons.mp hMem with rfl | hMem
    · exact hSuccessors
    · exact hInv.other o hMem hB
  · rw [hInv.opList block blockIn]
    simp only [hIff]

theorem PhaseA.step_branch {ctx₀ ctx ctx' : WfIRContext OpCode} {done : List OperationPtr}
    {compareOf regOp newBranch} {op : OperationPtr} {regOps : Array OperationPtr}
    {newOp : OperationPtr}
    (hInv : PhaseA ctx₀ ctx done compareOf regOp newBranch)
    (opIn₀ : op.InBounds ctx₀.raw) (hNotDone : op ∉ done)
    (hBranch : op.IsGmirBranch ctx₀.raw) (hResults : op.getNumResults! ctx₀.raw = 0)
    (hStep : BranchStep ctx ctx' op (compareOf op) regOps newOp) :
    PhaseA ctx₀ ctx' (op :: done) compareOf
      (fun o i => if o = op then regOps[i]! else regOp o i)
      (fun o => if o = op then newOp else newBranch o) := by
  have hSame := hInv.ops op opIn₀ (fun h => hNotDone h.1)
  have opIn := hSame.inBounds
  have hBranchCtx : op.IsGmirBranch ctx.raw := by
    simpa [OperationPtr.IsGmirBranch, hSame.opType] using hBranch
  have hRegOperands : regOperands ctx.raw op (compareOf op) =
      regOperands ctx₀.raw op (compareOf op) :=
    regOperands_congr (by rw [hSame.operands]; simp)
  /- An operation of `ctx` that is not the branch stays the same. -/
  have hOther : ∀ o', o'.InBounds ctx.raw → ¬ o'.IsGmirBranch ctx.raw →
      OpSame id ctx.raw ctx'.raw o' :=
    fun o' oIn' hB => hStep.ops o' oIn' (fun hEq => hB (hEq ▸ hBranchCtx))
  have hSize : regOps.size = (regOperands ctx₀.raw op (compareOf op)).length :=
    hStep.size.trans (by rw [hRegOperands])
  refine ⟨fun o oIn hNot => ?_, hInv.ctxSame.trans hStep.ctxSame, fun v vIn => ?_,
    fun o hMem hB => ?_, fun o hMem hB => ?_, fun block blockIn => ?_⟩
  · have hNe : o ≠ op := fun hEq => hNot ⟨by simp [hEq], hEq ▸ hBranch⟩
    have hOld := hInv.ops o oIn (fun h => hNot ⟨List.mem_cons_of_mem _ h.1, h.2⟩)
    exact hOld.trans_id (hStep.ops o hOld.inBounds hNe)
  · have h₁ := hInv.types v vIn
    have h₂ := hStep.types v h₁.1 (fun r hr hEq => by
      subst hr
      obtain ⟨_, hIndex⟩ := OpResultPtr.inBounds_def.mp (by simpa using h₁.1)
      have : op.getNumResults! ctx.raw = 0 := by
        rw [← OperationPtr.getResultTypes!.size_eq_getNumResults!, hSame.resultTypes,
          OperationPtr.getResultTypes!.size_eq_getNumResults!, hResults]
      grind)
    exact ⟨h₂.1, h₂.2.trans h₁.2⟩
  · rcases List.mem_cons.mp hMem with rfl | hMem
    · exact absurd hBranch hB
    · exact hInv.other o hMem hB
  · by_cases hEq : o = op
    · subst hEq
      simp only [↓reduceIte]
      have hGet : ∀ i (hi : i < (regOperands ctx₀.raw o (compareOf o)).length),
          regOps[i]! = regOps[i]'(hSize ▸ hi) :=
        fun i hi => getElem!_pos regOps i (hSize ▸ hi)
      have hBrcond : o.getOpType! ctx₀.raw = .gmir .g_brcond → o.getOpType! ctx.raw ≠ .gmir .g_br :=
        fun hB => by rw [hSame.opType, hB]; simp
      refine ⟨hResults, fun i hi => ?_, fun i j hi hj hEq => ?_, hStep.newIn,
        hStep.newResultTypes, hStep.newSuccessors.trans hSame.successors, ?_,
        fun hB => hStep.newBr (hSame.opType.trans hB), fun hB hc => ?_,
        fun hB branch l r hc => ?_⟩
      · rw [hGet i hi]
        obtain ⟨c₁, c₂, c₃⟩ := hStep.regOp i (hSize ▸ hi) (by rw [hRegOperands]; exact hi)
        refine ⟨c₁, fun r rIn hr => ?_, ?_⟩
        · obtain ⟨rOpIn, hIndex⟩ := OpResultPtr.inBounds_def.mp rIn
          have hNotLowered : ¬ (r.op ∈ done ∧ r.op.IsGmirBranch ctx₀.raw) := fun h => by
            have := (hInv.branch r.op h.1 h.2).numResults
            grind
          exact c₂ (hr ▸ (hInv.ops r.op rOpIn hNotLowered).inBounds)
        · have hEq : (regOperands ctx₀.raw o (compareOf o))[i]?.join =
              (regOperands ctx.raw o (compareOf o))[i]'(by rw [hRegOperands]; exact hi) := by
            simp [hRegOperands, List.getElem?_eq_getElem hi]
          rw [hEq]; exact c₃
      · rw [hGet i hi, hGet j hj] at hEq
        exact hStep.nodup.eq_of_getElem_eq (by simpa [hSize] using hi) (by simpa [hSize] using hj)
          (by simpa using hEq)
      · rw [hStep.newOperands]
        apply Array.ext
        · simp [hSize]
        · intro i h₁ h₂
          simp only [Array.getElem_map, Array.getElem_range]
          rw [getElem!_pos regOps i (by simpa using h₁)]
      · exact ⟨(hStep.newBnez (hBrcond hB) hc).1,
          by rw [(hStep.newBnez (hBrcond hB) hc).2, hSame.properties]⟩
      · exact ⟨(hStep.newCompare (hBrcond hB) branch l r hc).1,
          by rw [(hStep.newCompare (hBrcond hB) branch l r hc).2, hSame.properties]⟩
    · have hMem' : o ∈ done := by simpa [hEq] using hMem
      simp only [hEq, ↓reduceIte]
      exact (hInv.branch o hMem' hB).mono hB hOther
  · rw [hStep.opList block (hInv.ctxSame.blockIn blockIn), hInv.opList block blockIn]
    simp only [List.replaceBy, List.flatMap_assoc]
    congr 1
    funext o
    by_cases hEq : o = op
    · subst hEq
      simp only [hNotDone, false_and, ↓reduceIte, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.mem_cons, true_or, hBranch, and_self, loweredOps]
      rw [Array.toList_eq_map_range, hSize]
    · by_cases hLowered : o ∈ done ∧ o.IsGmirBranch ctx₀.raw
      · have hFacts := hInv.branch o hLowered.1 hLowered.2
        have hMem : o ∈ op :: done := List.mem_cons_of_mem _ hLowered.1
        simp only [hLowered, and_self, ↓reduceIte, hMem, hEq, loweredOps]
        /- Neither a register nor a RISC-V branch is the gMIR branch that is lowered now. -/
        have hNot := hFacts.not_isGmirBranch hLowered.2
        have hNotMem : op ∉ (List.range (regOperands ctx₀.raw o (compareOf o)).length).map
            (regOp o) ++ [newBranch o] := by
          intro hOp
          rcases List.mem_append.mp hOp with hOp | hOp
          · obtain ⟨i, hi, hReg⟩ := List.mem_map.mp hOp
            exact hNot.2 i (by simpa using hi) (hReg ▸ hBranchCtx)
          · obtain rfl : op = newBranch o := by simpa using hOp
            exact hNot.1 hBranchCtx
        exact List.replaceBy_of_not_mem hNotMem
      · simp [hLowered, hEq]

theorem PhaseA.step {ctx₀ ctx ctx' : WfIRContext OpCode} {done : List OperationPtr}
    {compareOf regOp newBranch} {op : OperationPtr} {convertible : BlockPtr → Bool}
    (hInv : PhaseA ctx₀ ctx done compareOf regOp newBranch)
    (opIn₀ : op.InBounds ctx₀.raw) (hNotDone : op ∉ done)
    (hNotUnreachable : op.getOpType! ctx₀.raw ≠ OpCode.llvm .unreachable)
    (hSuccessors : ¬ op.IsGmirBranch ctx₀.raw → op.getNumSuccessors! ctx₀.raw = 0)
    (hConvertible : op.IsGmirBranch ctx₀.raw → (op.getSuccessors! ctx₀.raw).all convertible)
    (hCounts : op.IsGmirBranch ctx₀.raw →
      op.getNumResults! ctx₀.raw = 0 ∧ op.getNumRegions! ctx₀.raw = 0)
    (h : convertBranch convertible compareOf ctx op = .ok ctx') :
    ∃ regOp' newBranch', PhaseA ctx₀ ctx' (op :: done) compareOf regOp' newBranch' := by
  have hSame := hInv.ops op opIn₀ (fun h => hNotDone h.1)
  have hBranchIff : op.IsGmirBranch ctx.raw ↔ op.IsGmirBranch ctx₀.raw := by
    simp [OperationPtr.IsGmirBranch, hSame.opType]
  rcases convertBranch_ok hSame.inBounds (by rw [hSame.opType]; exact hNotUnreachable)
      (fun hB => by
        have hC := hCounts (hBranchIff.mp hB)
        refine ⟨?_, by rw [hSame.numRegions]; exact hC.2⟩
        rw [← OperationPtr.getResultTypes!.size_eq_getNumResults!, hSame.resultTypes,
          OperationPtr.getResultTypes!.size_eq_getNumResults!]
        exact hC.1) h with
    ⟨hBranch, rfl⟩ | ⟨hBranch, hGate, -⟩ | ⟨hBranch, regOps, newOp, hStep⟩
  · exact ⟨regOp, newBranch, hInv.step_other (by rwa [← hBranchIff])
      (hSuccessors (by rwa [← hBranchIff]))⟩
  · exact absurd (hSame.successors ▸ hConvertible (hBranchIff.mp hBranch)) hGate
  · exact ⟨_, _, hInv.step_branch opIn₀ hNotDone (hBranchIff.mp hBranch)
      (hCounts (hBranchIff.mp hBranch)).1 hStep⟩

theorem PhaseA.foldlM {ctx₀ ctx ctx' : WfIRContext OpCode} {done rest : List OperationPtr}
    {compareOf regOp newBranch} {convertible : BlockPtr → Bool}
    (hInv : PhaseA ctx₀ ctx done compareOf regOp newBranch)
    (restIn : ∀ o ∈ rest, o.InBounds ctx₀.raw) (hNodup : rest.Nodup)
    (hDisjoint : ∀ o ∈ rest, o ∉ done)
    (hNotUnreachable : ∀ o ∈ rest, o.getOpType! ctx₀.raw ≠ OpCode.llvm .unreachable)
    (hSuccessors : ∀ o ∈ rest, ¬ o.IsGmirBranch ctx₀.raw → o.getNumSuccessors! ctx₀.raw = 0)
    (hConvertible : ∀ o ∈ rest, o.IsGmirBranch ctx₀.raw →
      (o.getSuccessors! ctx₀.raw).all convertible)
    (hCounts : ∀ o ∈ rest, o.IsGmirBranch ctx₀.raw →
      o.getNumResults! ctx₀.raw = 0 ∧ o.getNumRegions! ctx₀.raw = 0)
    (h : rest.foldlM (convertBranch convertible compareOf) ctx = .ok ctx') :
    ∃ done' regOp' newBranch', PhaseA ctx₀ ctx' done' compareOf regOp' newBranch' ∧
      ∀ o, o ∈ done' ↔ o ∈ rest ∨ o ∈ done := by
  induction rest generalizing ctx done regOp newBranch with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨done, regOp, newBranch, hInv, by simp⟩
  | cons op rest ih =>
    simp only [List.foldlM_cons, bind, Except.bind] at h
    split at h
    next => simp at h
    next ctx₁ hStep =>
      obtain ⟨regOp₁, newBranch₁, hInv₁⟩ :=
        hInv.step (restIn op (by simp)) (hDisjoint op (by simp))
          (hNotUnreachable op (by simp)) (hSuccessors op (by simp)) (hConvertible op (by simp))
          (hCounts op (by simp)) hStep
      have hNodup' := List.nodup_cons.mp hNodup
      obtain ⟨done', regOp', newBranch', hInv', hMem⟩ := ih hInv₁
        (fun o ho => restIn o (by simp [ho])) hNodup'.2
        (fun o ho hMem => by
          rcases List.mem_cons.mp hMem with rfl | hMem
          · exact hNodup'.1 ho
          · exact hDisjoint o (by simp [ho]) hMem)
        (fun o ho => hNotUnreachable o (by simp [ho])) (fun o ho => hSuccessors o (by simp [ho]))
        (fun o ho => hConvertible o (by simp [ho])) (fun o ho => hCounts o (by simp [ho])) h
      exact ⟨done', regOp', newBranch', hInv', fun o => by
        rw [hMem o]; simp only [List.mem_cons]; grind⟩

/-! ## Converting the arguments of a block -/

theorem convertBlockArgument_ok {block : BlockPtr} {ctx ctx' : WfIRContext OpCode} {i : Nat}
    (h : convertBlockArgument block ctx i = .ok ctx') :
    let arg : BlockArgumentPtr := ⟨block, i⟩
    let ctx₁ := WfRewriter.setType! ctx (.blockArgument arg) (RegisterType.mk : TypeAttr)
    ∃ ctx₂ cast,
      WfRewriter.createOp! ctx₁ (OpCode.builtin .unrealized_conversion_cast)
        #[(ValuePtr.blockArgument arg).getType! ctx.raw] #[] #[] #[] default
        (some (InsertPoint.atStart! block ctx₁.raw)) = some (ctx₂, cast) ∧
      ctx' = WfRewriter.pushOperand!
        (WfRewriter.replaceValue! ctx₂ (.blockArgument arg) (cast.getResult 0)) cast
        (.blockArgument arg) := by
  simp only [convertBlockArgument] at h
  split at h
  next ctx₂ cast hCreate =>
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact ⟨ctx₂, cast, hCreate, h.symm⟩
  next => simp [throw, throwThe, MonadExceptOf.throw] at h

/-- The value that stands for `value` once the uses of `arg` are uses of `cast`. -/
@[expose]
def substArg (arg : BlockArgumentPtr) (cast : OperationPtr) (value : ValuePtr) : ValuePtr :=
  if value = .blockArgument arg then cast.getResult 0 else value

/-- What converting the block argument `arg` does: `cast` gives it its original type. -/
structure ArgStep (ctx ctx' : WfIRContext OpCode) (arg : BlockArgumentPtr) (cast : OperationPtr) :
    Prop where
  ops : ∀ o, o.InBounds ctx.raw → OpSame (substArg arg cast) ctx.raw ctx'.raw o
  ctxSame : CtxSame ctx.raw ctx'.raw
  types : ∀ value : ValuePtr, value.InBounds ctx.raw →
    value.InBounds ctx'.raw ∧ value.getType! ctx'.raw =
      if value = .blockArgument arg then (RegisterType.mk : TypeAttr) else value.getType! ctx.raw
  castIn : cast.InBounds ctx'.raw
  castNotIn : ¬ cast.InBounds ctx.raw
  castType : cast.getOpType! ctx'.raw = .builtin .unrealized_conversion_cast
  castResultTypes : cast.getResultTypes! ctx'.raw = #[(ValuePtr.blockArgument arg).getType! ctx.raw]
  castOperands : cast.getOperands! ctx'.raw = #[.blockArgument arg]
  opList : ∀ (block : BlockPtr) (blockIn : block.InBounds ctx.raw),
    block.opList ctx' (ctxSame.blockIn blockIn) =
      if block = arg.block then cast :: block.opList ctx blockIn else block.opList ctx blockIn

theorem convertBlockArgument_spec {ctx ctx' : WfIRContext OpCode} {arg : BlockArgumentPtr}
    (argIn : arg.InBounds ctx.raw)
    (h : convertBlockArgument arg.block ctx arg.index = .ok ctx') :
    ∃ cast, ArgStep ctx ctx' arg cast := by
  obtain ⟨ctx₂, cast, hCreate, rfl⟩ := convertBlockArgument_ok h
  have hArg : (⟨arg.block, arg.index⟩ : BlockArgumentPtr) = arg := rfl
  simp only [hArg] at hCreate ⊢
  have valueIn : (ValuePtr.blockArgument arg).InBounds ctx.raw := by simpa using argIn
  have blockIn : arg.block.InBounds ctx.raw := (BlockArgumentPtr.inBounds_def.mp argIn).1
  rw [WfRewriter.setType!_eq valueIn] at hCreate
  obtain ⟨hOps₁, hCtx₁, hIn₁, hTypes₁, hList₁⟩ := WfRewriter.setType_frame (ctx := ctx)
    (arg := arg) (type := (RegisterType.mk : TypeAttr)) (argIn := valueIn)
  generalize WfRewriter.setType ctx (.blockArgument arg) (RegisterType.mk : TypeAttr) valueIn = ctx₁
    at hCreate hOps₁ hCtx₁ hIn₁ hTypes₁ hList₁
  obtain ⟨h₁, h₂, h₃, h₄, hCreate⟩ := WfRewriter.createOp_of_createOp! hCreate
  obtain ⟨hNotIn₂, hIn₂, hOps₂, hCtx₂, hTypes₂, hType₂, hResultTypes₂, hOperands₂, _⟩ :=
    WfRewriter.createOp_frame hCreate
  have hMono₂ : ∀ ptr : GenericPtr, ptr.InBounds ctx₁.raw → ptr.InBounds ctx₂.raw :=
    fun ptr => WfRewriter.createOp_inBounds_mono hCreate
  have hList₂ := fun (block : BlockPtr) (bIn : block.InBounds ctx₁.raw) (bIn' : block.InBounds ctx₂.raw) =>
    WfRewriter.createOp_atStart_opList hCreate (hCtx₁.blockIn blockIn) bIn bIn'
  /- The uses of the argument become uses of the cast. -/
  have valueIn₂ : (ValuePtr.blockArgument arg).InBounds ctx₂.raw := by
    have := hMono₂ (.value (.blockArgument arg)) ((hIn₁ _).mpr (by simpa using valueIn))
    simpa using this
  have castNum : cast.getNumResults! ctx₂.raw = 1 := by
    rw [← OperationPtr.getResultTypes!.size_eq_getNumResults!, hResultTypes₂]; rfl
  have resultIn₂ : (ValuePtr.opResult (cast.getResult 0)).InBounds ctx₂.raw := by
    simp only [ValuePtr.inBounds_opResult, OperationPtr.getResult_def]
    exact OpResultPtr.inBounds_def.mpr ⟨hIn₂, by grind⟩
  have hNe : ValuePtr.blockArgument arg ≠ ValuePtr.opResult (cast.getResult 0) := by simp
  rw [WfRewriter.replaceValue!_eq hNe valueIn₂ resultIn₂]
  obtain ⟨hOps₃, hCtx₃, hIn₃, hTypes₃⟩ := WfRewriter.replaceValue_frame (ctx := ctx₂)
    (hNe := hNe) (oldIn := valueIn₂) (newIn := resultIn₂)
  have hList₃ := fun (block : BlockPtr) (bIn : block.InBounds ctx₂.raw) bIn' =>
    WfRewriter.replaceValue_opList (ctx := ctx₂) (hNe := hNe) (oldIn := valueIn₂)
      (newIn := resultIn₂) (block := block) bIn bIn'
  generalize WfRewriter.replaceValue ctx₂ (.blockArgument arg) (.opResult (cast.getResult 0)) hNe
    valueIn₂ resultIn₂ = ctx₃ at hOps₃ hCtx₃ hIn₃ hTypes₃ hList₃
  /- The cast takes the argument, which is now a register. -/
  have castIn₃ : cast.InBounds ctx₃.raw := by
    have := (hIn₃ (.operation cast)).mpr (by simpa using hIn₂); simpa using this
  have valueIn₃ : (ValuePtr.blockArgument arg).InBounds ctx₃.raw := by
    have := (hIn₃ (.value (.blockArgument arg))).mpr (by simpa using valueIn₂); simpa using this
  rw [WfRewriter.pushOperand!_eq castIn₃ valueIn₃]
  obtain ⟨hOps₄, hCast₄, hCtx₄, hMono₄, hTypes₄, hList₄⟩ := WfRewriter.pushOperand_frame
    (ctx := ctx₃) (op := cast) (value := .blockArgument arg) (opIn := castIn₃) (valueIn := valueIn₃)
  generalize WfRewriter.pushOperand ctx₃ cast (.blockArgument arg) castIn₃ valueIn₃ = ctx₄
    at hOps₄ hCast₄ hCtx₄ hMono₄ hTypes₄ hList₄
  have hNotIn : ¬ cast.InBounds ctx.raw := fun h =>
    hNotIn₂ (by have := (hIn₁ (.operation cast)).mpr (by simpa using h); simpa using this)
  have hCastSame₃ := hOps₃ cast hIn₂
  refine ⟨cast, {
    ops := fun o oIn => ?_
    ctxSame := ((hCtx₁.trans hCtx₂).trans hCtx₃).trans hCtx₄
    types := fun v vIn => ?_
    castIn := hCast₄.1
    castNotIn := hNotIn
    castType := hCast₄.2.1.trans (hCastSame₃.opType.trans (hType₂.trans (ofDialect_self _)))
    castResultTypes := hCast₄.2.2.1.trans (hCastSame₃.resultTypes.trans hResultTypes₂)
    castOperands := by rw [hCast₄.2.2.2, hCastSame₃.operands, hOperands₂]; simp
    opList := fun block bIn => ?_ }⟩
  · have s₁ := hOps₁ o oIn
    have s₂ := hOps₂ o s₁.inBounds
    have s₃ := hOps₃ o s₂.inBounds
    have hNeCast : o ≠ cast := fun hEq => hNotIn (hEq ▸ oIn)
    have s₄ := hOps₄ o s₃.inBounds hNeCast
    exact (((s₁.trans_id s₂).trans s₃).trans_id s₄).congr (fun _ _ => rfl)
  · have v₁ : v.InBounds ctx₁.raw := by
      have := (hIn₁ (.value v)).mpr (by simpa using vIn); simpa using this
    have v₂ : v.InBounds ctx₂.raw := by
      have := hMono₂ (.value v) (by simpa using v₁); simpa using this
    have v₃ : v.InBounds ctx₃.raw := by
      have := (hIn₃ (.value v)).mpr (by simpa using v₂); simpa using this
    refine ⟨by have := hMono₄ (.value v) (by simpa using v₃); simpa using this, ?_⟩
    rw [hTypes₄, hTypes₃, hTypes₂ v v₁, hTypes₁]
  · have b₁ := hCtx₁.blockIn bIn
    have b₂ := hCtx₂.blockIn b₁
    have b₃ := hCtx₃.blockIn b₂
    rw [hList₄ block b₃, hList₃ block b₂, hList₂ block b₁, hList₁ block bIn]

/-! ## Converting all block arguments -/

/-- The value that stands for `value` once the arguments `done` are converted. -/
@[expose]
def lowerArgs (done : List BlockArgumentPtr) (argCast : BlockArgumentPtr → OperationPtr)
    (value : ValuePtr) : ValuePtr :=
  match value with
  | .blockArgument arg => if arg ∈ done then (argCast arg).getResult 0 else value
  | .opResult _ => value

/-- The module after the block arguments `done` were converted, latest first. -/
structure PhaseB (ctx₀ ctx : WfIRContext OpCode) (done : List BlockArgumentPtr)
    (argCast : BlockArgumentPtr → OperationPtr) : Prop where
  ops : ∀ o, o.InBounds ctx₀.raw → OpSame (lowerArgs done argCast) ctx₀.raw ctx.raw o
  ctxSame : CtxSame ctx₀.raw ctx.raw
  types : ∀ value : ValuePtr, value.InBounds ctx₀.raw →
    value.InBounds ctx.raw ∧ value.getType! ctx.raw =
      if (∃ arg ∈ done, value = .blockArgument arg) then (RegisterType.mk : TypeAttr)
      else value.getType! ctx₀.raw
  args : ∀ arg ∈ done, arg.InBounds ctx₀.raw ∧
    (argCast arg).InBounds ctx.raw ∧ ¬ (argCast arg).InBounds ctx₀.raw ∧
    (argCast arg).getOpType! ctx.raw = .builtin .unrealized_conversion_cast ∧
    (argCast arg).getResultTypes! ctx.raw = #[(ValuePtr.blockArgument arg).getType! ctx₀.raw] ∧
    (argCast arg).getOperands! ctx.raw = #[.blockArgument arg]
  inj : ∀ arg₁ ∈ done, ∀ arg₂ ∈ done, argCast arg₁ = argCast arg₂ → arg₁ = arg₂
  opList : ∀ (block : BlockPtr) (blockIn : block.InBounds ctx₀.raw),
    block.opList ctx (ctxSame.blockIn blockIn) =
      (done.filter (·.block = block)).map argCast ++ block.opList ctx₀ blockIn

theorem PhaseB.init {ctx₀ : WfIRContext OpCode} {argCast} : PhaseB ctx₀ ctx₀ [] argCast :=
  ⟨fun o oIn => (OpSame.refl oIn).congr (fun v _ => by cases v <;> simp [lowerArgs]),
    CtxSame.refl, fun _ vIn => ⟨vIn, by simp⟩, fun _ h => by simp at h,
    fun _ h => by simp at h, fun _ _ => by simp⟩

theorem PhaseB.step {ctx₀ ctx ctx' : WfIRContext OpCode} {done : List BlockArgumentPtr}
    {argCast} {arg : BlockArgumentPtr} {cast : OperationPtr}
    (hInv : PhaseB ctx₀ ctx done argCast) (argIn₀ : arg.InBounds ctx₀.raw)
    (hNotDone : arg ∉ done) (hStep : ArgStep ctx ctx' arg cast) :
    PhaseB ctx₀ ctx' (arg :: done) (fun a => if a = arg then cast else argCast a) := by
  have hOld : ∀ a ∈ done, a ≠ arg := fun a ha hEq => hNotDone (hEq ▸ ha)
  refine ⟨fun o oIn => ?_, hInv.ctxSame.trans hStep.ctxSame, fun v vIn => ?_, fun a ha => ?_,
    fun a₁ h₁ a₂ h₂ hEq => ?_, fun block blockIn => ?_⟩
  · have s₁ := hInv.ops o oIn
    refine (s₁.trans (hStep.ops o s₁.inBounds)).congr (fun v _ => ?_)
    rcases v with r | a
    · simp [lowerArgs, substArg]
    · by_cases hEq : a = arg
      · subst hEq; simp [lowerArgs, substArg, hNotDone]
      · by_cases hDone : a ∈ done
        · simp [lowerArgs, substArg, hDone, hEq]
        · simp [lowerArgs, substArg, hDone, hEq]
  · have h₁ := hInv.types v vIn
    have h₂ := hStep.types v h₁.1
    refine ⟨h₂.1, ?_⟩
    rw [h₂.2, h₁.2]
    by_cases hEq : v = .blockArgument arg
    · simp [hEq]
    · by_cases hDone : ∃ a ∈ done, v = .blockArgument a
      · obtain ⟨a, ha, rfl⟩ := hDone
        simp [hEq, ha]
      · simp [hEq, hDone]
  · rcases List.mem_cons.mp ha with rfl | ha
    · simp only [↓reduceIte]
      have := (hInv.types (.blockArgument a) (by simpa using argIn₀)).2
      have hNo : ¬ ∃ a' ∈ done, ValuePtr.blockArgument a = .blockArgument a' := by
        rintro ⟨a', ha', hEq⟩
        simp only [ValuePtr.blockArgument.injEq] at hEq
        exact hNotDone (hEq ▸ ha')
      simp only [hNo, ↓reduceIte] at this
      exact ⟨argIn₀, hStep.castIn,
        fun h => hStep.castNotIn (hInv.ops _ h).inBounds, hStep.castType,
        this ▸ hStep.castResultTypes, hStep.castOperands⟩
    · obtain ⟨c₁, c₂, c₃, c₄, c₅, c₆⟩ := hInv.args a ha
      have hS := hStep.ops (argCast a) c₂
      simp only [hOld a ha, ↓reduceIte]
      refine ⟨c₁, hS.inBounds, c₃, hS.opType.trans c₄, hS.resultTypes.trans c₅, ?_⟩
      rw [hS.operands, c₆]
      simp [substArg, hOld a ha]
  · by_cases e₁ : a₁ = arg <;> by_cases e₂ : a₂ = arg
    · rw [e₁, e₂]
    · have m₂ : a₂ ∈ done := by simpa [e₂] using h₂
      simp only [e₁, e₂, ↓reduceIte] at hEq
      exact absurd (hEq ▸ (hInv.args a₂ m₂).2.1) hStep.castNotIn
    · have m₁ : a₁ ∈ done := by simpa [e₁] using h₁
      simp only [e₁, e₂, ↓reduceIte] at hEq
      exact absurd (hEq ▸ (hInv.args a₁ m₁).2.1) hStep.castNotIn
    · simp only [e₁, e₂, ↓reduceIte] at hEq
      exact hInv.inj a₁ (by simpa [e₁] using h₁) a₂ (by simpa [e₂] using h₂) hEq
  · rw [hStep.opList block (hInv.ctxSame.blockIn blockIn), hInv.opList block blockIn]
    have hMap : (done.filter (·.block = block)).map (fun a => if a = arg then cast else argCast a) =
        (done.filter (·.block = block)).map argCast :=
      List.map_congr_left (fun a ha => by simp [hOld a (List.mem_filter.mp ha).1])
    by_cases hBlock : block = arg.block
    · subst hBlock; simp [hMap]
    · have : ¬ arg.block = block := fun h => hBlock h.symm
      simp [hMap, hBlock, this]

theorem PhaseB.foldArgs {ctx₀ ctx ctx' : WfIRContext OpCode} {done : List BlockArgumentPtr}
    {argCast} {block : BlockPtr} {indices : List Nat}
    (hInv : PhaseB ctx₀ ctx done argCast)
    (hIndices : ∀ i ∈ indices, (⟨block, i⟩ : BlockArgumentPtr).InBounds ctx₀.raw)
    (hNodup : indices.Nodup)
    (hNotDone : ∀ i ∈ indices, (⟨block, i⟩ : BlockArgumentPtr) ∉ done)
    (h : indices.foldlM (convertBlockArgument block) ctx = .ok ctx') :
    ∃ argCast', PhaseB ctx₀ ctx' (indices.reverse.map (⟨block, ·⟩) ++ done) argCast' := by
  induction indices generalizing ctx done argCast with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨argCast, by simpa using hInv⟩
  | cons i indices ih =>
    simp only [List.foldlM_cons, bind, Except.bind] at h
    split at h
    next => simp at h
    next ctx₁ hStep =>
      have argIn₀ := hIndices i (by simp)
      have argIn : (⟨block, i⟩ : BlockArgumentPtr).InBounds ctx.raw := by
        simpa using (hInv.types (.blockArgument ⟨block, i⟩) (by simpa using argIn₀)).1
      obtain ⟨cast, hArg⟩ := convertBlockArgument_spec (arg := ⟨block, i⟩) argIn hStep
      have hInv₁ := hInv.step argIn₀ (hNotDone i (by simp)) hArg
      have hNodup' := List.nodup_cons.mp hNodup
      obtain ⟨argCast', hInv'⟩ := ih hInv₁ (fun j hj => hIndices j (by simp [hj])) hNodup'.2
        (fun j hj hMem => by
          rcases List.mem_cons.mp hMem with hEq | hMem
          · simp only [BlockArgumentPtr.mk.injEq, true_and] at hEq
            exact hNodup'.1 (hEq ▸ hj)
          · exact hNotDone j (by simp [hj]) hMem) h
      exact ⟨argCast', by simpa using hInv'⟩

/-- The arguments of `block`, latest converted first. -/
@[expose]
def blockArgs (ctx : IRContext OpCode) (block : BlockPtr) : List BlockArgumentPtr :=
  (List.range (block.getNumArguments! ctx)).map (⟨block, ·⟩)

/-- The module after the blocks `blocks` were converted. -/
structure PhaseBlocks (ctx₀ ctx : WfIRContext OpCode) (blocks : List BlockPtr)
    (done : List BlockArgumentPtr) (argCast : BlockArgumentPtr → OperationPtr) : Prop where
  phase : PhaseB ctx₀ ctx done argCast
  blocksIn : ∀ block ∈ blocks, block.InBounds ctx₀.raw
  argsOf : ∀ block : BlockPtr, done.filter (·.block = block) =
    if block ∈ blocks then blockArgs ctx₀.raw block else []

theorem PhaseBlocks.step {ctx₀ ctx ctx' : WfIRContext OpCode} {blocks : List BlockPtr}
    {done : List BlockArgumentPtr} {argCast} {block : BlockPtr}
    (hInv : PhaseBlocks ctx₀ ctx blocks done argCast) (blockIn₀ : block.InBounds ctx₀.raw)
    (hNotDone : block ∉ blocks) (h : convertBlock ctx block = .ok ctx') :
    ∃ done' argCast', PhaseBlocks ctx₀ ctx' (block :: blocks) done' argCast' := by
  have hFold : (List.range (block.getNumArguments! ctx.raw)).reverse.foldlM
      (convertBlockArgument block) ctx = .ok ctx' := h
  have hNum := hInv.phase.ctxSame.numArguments blockIn₀
  rw [hNum] at hFold
  have hNone : ∀ arg ∈ done, arg.block ≠ block := fun arg hArg hEq => by
    have := hInv.argsOf block
    simp only [hNotDone, ↓reduceIte] at this
    have hMem : arg ∈ done.filter (·.block = block) := List.mem_filter.mpr ⟨hArg, by simp [hEq]⟩
    simp [this] at hMem
  obtain ⟨argCast', hPhase⟩ := hInv.phase.foldArgs (block := block)
    (indices := (List.range (block.getNumArguments! ctx₀.raw)).reverse)
    (fun i hi => BlockArgumentPtr.inBounds_def.mpr ⟨blockIn₀, by
      have : i < block.getNumArguments! ctx₀.raw := by simpa using hi
      grind⟩)
    (by
      have h : (List.range (block.getNumArguments! ctx₀.raw)).Nodup := List.nodup_range
      simpa [List.Nodup, List.pairwise_reverse] using h.imp Ne.symm)
      (fun i _ hMem => hNone _ hMem rfl) hFold
  refine ⟨_, argCast', hPhase, fun b hb => ?_, fun b => ?_⟩
  · rcases List.mem_cons.mp hb with rfl | hb
    · exact blockIn₀
    · exact hInv.blocksIn b hb
  · rw [List.filter_append]
    by_cases hEq : b = block
    · subst hEq
      have hDone := hInv.argsOf b
      simp only [hNotDone, ↓reduceIte] at hDone
      rw [hDone, List.append_nil, List.filter_eq_self.mpr (by simp)]
      simp [blockArgs]
    · have hFirst : ((List.range (block.getNumArguments! ctx₀.raw)).reverse.reverse.map
          (fun i => (⟨block, i⟩ : BlockArgumentPtr))).filter (·.block = b) = [] := by
        rw [List.filter_eq_nil_iff]
        intro a ha
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
        simpa using fun h => hEq h.symm
      rw [hFirst, List.nil_append, hInv.argsOf b]
      simp [hEq]

theorem PhaseBlocks.foldlM {ctx₀ ctx ctx' : WfIRContext OpCode} {blocks targets : List BlockPtr}
    {done : List BlockArgumentPtr} {argCast}
    (hInv : PhaseBlocks ctx₀ ctx blocks done argCast)
    (targetsIn : ∀ block ∈ targets, block.InBounds ctx₀.raw)
    (hNodup : targets.Nodup) (hFresh : ∀ block ∈ targets, block ∉ blocks)
    (h : targets.foldlM convertBlock ctx = .ok ctx') :
    ∃ blocks' done' argCast', PhaseBlocks ctx₀ ctx' blocks' done' argCast' ∧
      ∀ block, block ∈ blocks' ↔ block ∈ targets ∨ block ∈ blocks := by
  induction targets generalizing ctx blocks done argCast with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    exact ⟨blocks, done, argCast, h ▸ hInv, by simp⟩
  | cons block targets ih =>
    simp only [List.foldlM_cons, bind, Except.bind] at h
    split at h
    next => simp at h
    next ctx₁ hConvert =>
      obtain ⟨done₁, argCast₁, hInv₁⟩ :=
        hInv.step (targetsIn block (by simp)) (hFresh block (by simp)) hConvert
      obtain ⟨blocks', done', argCast', hInv', hIff⟩ := ih hInv₁
        (fun b hb => targetsIn b (by simp [hb])) (List.nodup_cons.mp hNodup).2
        (fun b hb => by
          simp only [List.mem_cons, not_or]
          exact ⟨fun hEq => (List.nodup_cons.mp hNodup).1 (hEq ▸ hb),
            hFresh b (by simp [hb])⟩) h
      exact ⟨blocks', done', argCast', hInv', fun b => by
        rw [hIff b]; simp only [List.mem_cons]; grind⟩

/-! ## The compares the pass matches -/

theorem OperationPtr.getProperties!_gmir {op : OperationPtr} {ctx : IRContext OpCode}
    {opCode : GMIR} : op.getProperties! ctx opCode = op.getProperties! ctx (OpCode.gmir opCode) := by
  simp only [OperationPtr.getProperties!]
  rfl

theorem matchCompare_spec {ctx : WfIRContext OpCode} {op : OperationPtr} {c : Compare}
    (opIn : op.InBounds ctx.raw) (h : matchCompare ctx.raw op = some c) :
    ∃ icmp : OperationPtr, op.getOpType! ctx.raw = .gmir .g_brcond ∧
      op.getOperand! ctx.raw 0 = icmp.getResult 0 ∧ op.getPrevOp! ctx.raw = some icmp ∧
      icmp.getOpType! ctx.raw = .gmir .g_icmp ∧ icmp.getNumOperands! ctx.raw = 2 ∧
      icmp.getNumResults! ctx.raw = 1 ∧
      icmp.getOperand! ctx.raw 0 ≠ icmp.getResult 0 ∧
      icmp.getOperand! ctx.raw 1 ≠ icmp.getResult 0 ∧
      fillsRegister ((icmp.getOperand! ctx.raw 0).getType! ctx.raw) ∧
      compareBranch (icmp.getProperties! ctx.raw (OpCode.gmir .g_icmp)).predicate
        (icmp.getOperand! ctx.raw 0) (icmp.getOperand! ctx.raw 1)
        (matchGConstantIntVal (icmp.getOperand! ctx.raw 1) ctx.raw) = c := by
  simp only [matchCompare, bind, Option.bind] at h
  have hType : op.getOpType! ctx.raw = OpCode.gmir GMIR.g_brcond :=
    Classical.byContradiction fun hNot => by simp [hNot, guard] at h
  simp only [hType, guard, ↓reduceIte] at h
  obtain ⟨r, hCond⟩ : ∃ r, op.getOperand! ctx.raw 0 = .opResult r := by
    rcases hCond : op.getOperand! ctx.raw 0 with r | arg
    · exact ⟨r, rfl⟩
    · simp [hCond] at h
  simp only [hCond] at h
  have hPrev : op.getPrevOp! ctx.raw = some r.op :=
    Classical.byContradiction fun hNot => by simp [hNot] at h
  simp only [hPrev, ↓reduceIte] at h
  obtain ⟨⟨operands, props⟩, hMatch⟩ : ∃ m, matchOp r.op ctx.raw GMIR.g_icmp 2 = some m := by
    rcases hMatch : matchOp r.op ctx.raw GMIR.g_icmp 2 with _ | m
    · simp [hMatch] at h
    · exact ⟨m, rfl⟩
  simp only [hMatch] at h
  obtain ⟨hIcmpType, hNumOps, hNumRes, rfl, rfl⟩ := matchOp_implies hMatch
  simp only [OperationPtr.getOperands!.getElem!_eq_getOperand!] at h
  have hDistinct : r.op.getOperand! ctx.raw 0 ≠ .opResult r ∧
      r.op.getOperand! ctx.raw 1 ≠ .opResult r := by
    by_cases hA : r.op.getOperand! ctx.raw 0 = .opResult r <;>
      by_cases hB : r.op.getOperand! ctx.raw 1 = .opResult r
    · simp [hA, hB, failure] at h
    · simp [hA, hB, failure] at h
    · simp [hA, hB, failure] at h
    · exact ⟨hA, hB⟩
  simp only [hDistinct, ne_eq, not_false_eq_true, decide_true, Bool.and_self, ↓reduceIte] at h
  have hFills : fillsRegister ((r.op.getOperand! ctx.raw 0).getType! ctx.raw) :=
    Classical.byContradiction fun hNot => by simp [hNot] at h
  simp only [hFills, ↓reduceIte] at h
  /- The condition is the only result of the `g_icmp`. -/
  have hIndex : r.index = 0 := by
    by_cases h0 : 0 < op.getNumOperands! ctx.raw
    · have := OperationPtr.getOperands!_inBounds ctx.wellFormed.inBounds opIn
        (OperationPtr.getOperands!.mem_getOperand h0)
      rw [hCond] at this
      grind [OpResultPtr.inBounds_def]
    · have : op.getOperand! ctx.raw 0 = default := by
        simp only [OperationPtr.getOperand!]
        rw [getElem!_neg]
        · rfl
        · rw [← OperationPtr.getNumOperands!.eq_def] ; omega
      rw [hCond] at this
      cases this; rfl
  refine ⟨r.op, hType, ?_, hPrev, hIcmpType, hNumOps, hNumRes, ?_, ?_, hFills, ?_⟩
  · rw [hCond]; cases r; simp_all [OperationPtr.getResult_def]
  · have : (r.op.getResult 0 : ValuePtr) = .opResult r := by cases r; simp_all [OperationPtr.getResult_def]
    rw [this]; exact hDistinct.1
  · have : (r.op.getResult 0 : ValuePtr) = .opResult r := by cases r; simp_all [OperationPtr.getResult_def]
    rw [this]; exact hDistinct.2
  · rw [← OperationPtr.getProperties!_gmir]
    simpa [pure] using h

/-- The type of the only result of an operation is its first result type. -/
theorem OperationPtr.getResultTypes!_getElem?_zero {op : OperationPtr} {ctx : IRContext OpCode}
    (h : 0 < op.getNumResults! ctx) :
    (op.getResultTypes! ctx)[0]? = some ((op.getResult 0 : ValuePtr).getType! ctx) := by
  simp only [OperationPtr.getResultTypes!, OperationPtr.getNumResults!] at h ⊢
  simp only [ValuePtr.getType!_opResult, OpResultPtr.getType!, OpResultPtr.get!,
    OperationPtr.getResult_def]
  grind

/-- What `matchGConstantIntVal` matches: the result of a `g_constant` of integer type. -/
theorem matchGConstantIntVal_spec {ctx : WfIRContext OpCode} {value : ValuePtr} {k : Int}
    (valueIn : value.InBounds ctx.raw) (h : matchGConstantIntVal value ctx.raw = some k) :
    ∃ (constant : OperationPtr) (type : TypeAttr) (t : IntegerType),
      value = constant.getResult 0 ∧ constant.InBounds ctx.raw ∧
      constant.getOpType! ctx.raw = .gmir .g_constant ∧
      (constant.getResultTypes! ctx.raw)[0]? = some type ∧ type.val = .integerType t ∧
      k = (BitVec.ofInt t.bitwidth
        (constant.getProperties! ctx.raw (OpCode.gmir .g_constant)).value.value).toInt := by
  simp only [matchGConstantIntVal, bind, Option.bind] at h
  obtain ⟨r, rfl⟩ : ∃ r, value = .opResult r := by
    rcases value with r | arg
    · exact ⟨r, rfl⟩
    · simp at h
  simp only at h
  obtain ⟨⟨operands, props⟩, hMatch⟩ : ∃ m, matchOp r.op ctx.raw GMIR.g_constant 0 = some m := by
    rcases hMatch : matchOp r.op ctx.raw GMIR.g_constant 0 with _ | m
    · simp [hMatch] at h
    · exact ⟨m, rfl⟩
  simp only [hMatch] at h
  obtain ⟨hType, -, hNumRes, -, rfl⟩ := matchOp_implies hMatch
  obtain ⟨t, hT⟩ : ∃ t, ((ValuePtr.opResult r).getType! ctx.raw).val = .integerType t := by
    split at h
    next _ t hT => exact ⟨t, hT⟩
    next => simp at h
  simp only [hT] at h
  obtain ⟨opIn, hLt⟩ : r.op.InBounds ctx.raw ∧ r.index < r.op.getNumResults! ctx.raw := by
    grind [OpResultPtr.inBounds_def]
  have hIndex : r.index = 0 := by omega
  have hResult : (ValuePtr.opResult r) = r.op.getResult 0 := by
    cases r; simp_all [OperationPtr.getResult]
  refine ⟨r.op, _, t, hResult, opIn, hType,
    OperationPtr.getResultTypes!_getElem?_zero (by omega), by rw [← hResult]; exact hT, ?_⟩
  rw [← OperationPtr.getProperties!_gmir]
  simpa [pure] using h.symm

/-- The compares that `convertModule` matches up front are those `matchCompare` finds. -/
theorem getElem?_ofList_matchCompare {ctx : IRContext OpCode} {ops : List OperationPtr}
    (hNodup : ops.Nodup) {op : OperationPtr} (hOp : op ∈ ops) :
    (Std.HashMap.ofList (ops.filterMap fun o => (matchCompare ctx o).map (o, ·)))[op]? =
      matchCompare ctx op := by
  rcases hm : matchCompare ctx op with _ | c
  · apply Std.HashMap.getElem?_ofList_of_contains_eq_false
    simp only [List.contains_eq_any_beq, List.any_eq_false, List.mem_map, List.mem_filterMap,
      Option.map_eq_some_iff, beq_iff_eq]
    rintro _ ⟨⟨o, c'⟩, ⟨o', hO', c'', hc, hEq⟩, rfl⟩ rfl
    simp only [Prod.mk.injEq] at hEq
    obtain ⟨rfl, rfl⟩ := hEq
    simp_all
  · apply Std.HashMap.getElem?_ofList_of_mem (k := op) (beq_self_eq_true op)
    · rw [List.pairwise_filterMap]
      refine (List.nodup_iff_pairwise_ne.mp hNodup).imp fun {a b} hNe => ?_
      intro x hx y hy
      simp only [Option.map_eq_some_iff] at hx hy
      obtain ⟨_, -, rfl⟩ := hx
      obtain ⟨_, -, rfl⟩ := hy
      simpa using hNe
    · exact List.mem_filterMap.mpr ⟨op, hOp, by simp [hm]⟩

/-- The operation before `op` in the list of its block is the one `getPrevOp!` gives. -/
theorem getLast?_of_getPrevOp! {ctx : WfIRContext OpCode} {block : BlockPtr}
    (blockIn : block.InBounds ctx.raw) {pre post : List OperationPtr} {op prev : OperationPtr}
    (hList : (block.operationList ctx.raw ctx.wellFormed blockIn).toList = pre ++ op :: post)
    (hPrev : op.getPrevOp! ctx.raw = some prev) : pre.getLast? = some prev := by
  have hChain := BlockPtr.operationListWF ctx.raw block blockIn ctx.wellFormed
  generalize hArr : block.operationList ctx.raw ctx.wellFormed blockIn = arr at hList hChain
  have hLen : pre.length < arr.size := by
    have := congrArg List.length hList; simp at this; omega
  have hOp : arr[pre.length] = op := by
    have := congrArg (·[pre.length]?) hList
    simp only [Array.getElem?_toList, List.getElem?_append_right (Nat.le_refl _),
      Nat.sub_self, List.getElem?_cons_zero] at this
    rw [Array.getElem?_eq_getElem hLen] at this
    exact Option.some.inj this
  rcases pre.eq_nil_or_concat with rfl | ⟨pre', last, rfl⟩
  · have hFirst := hChain.first
    simp only [List.length_nil] at hOp hLen
    rw [Array.getElem?_eq_getElem hLen, hOp] at hFirst
    have := hChain.prevFirst hFirst
    rw [hPrev] at this
    cases this
  · have hLen' : pre'.length + 1 < arr.size := by simpa using hLen
    have hOp' : arr[pre'.length + 1] = op := by simpa using hOp
    have := hChain.prev (pre'.length + 1) (by omega) hLen'
    rw [hOp'] at this
    rw [hPrev] at this
    obtain rfl := Option.some.inj this
    have hLast : arr[pre'.length] = last := by
      have := congrArg (·[pre'.length]?) hList
      simp only [Array.getElem?_toList, List.concat_eq_append, List.append_assoc,
        List.singleton_append] at this
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero,
        Array.getElem?_eq_getElem (by omega)] at this
      exact Option.some.inj this
    simp [hLast]

/-! ## The modules the proof covers -/

/--
  The modules the proof covers: every operation with successors is a `g_br` or a
  `g_brcond`, and every value such a branch passes, and every argument of a block
  it branches to, round-trips through a register. The pass then leaves no branch
  alone and passes no pointer through a register.
-/
structure BranchesLowerable (ctx : WfIRContext OpCode) : Prop where
  successors : ∀ op : OperationPtr, op.InBounds ctx.raw → ¬ op.IsGmirBranch ctx.raw →
    op.getNumSuccessors! ctx.raw = 0
  operands : ∀ (op : OperationPtr) (i : Nat), op.InBounds ctx.raw → op.IsGmirBranch ctx.raw →
    i < op.getNumOperands! ctx.raw → roundTrips ((op.getOperand! ctx.raw i).getType! ctx.raw)
  arguments : ∀ (op : OperationPtr) (block : BlockPtr) (i : Nat), op.InBounds ctx.raw →
    op.IsGmirBranch ctx.raw → block ∈ op.getSuccessors! ctx.raw →
    i < block.getNumArguments! ctx.raw →
    roundTrips ((block.getArgument i : ValuePtr).getType! ctx.raw)

namespace BranchesLowerable

variable {ctx : WfIRContext OpCode} (hLowerable : BranchesLowerable ctx)
  {op : OperationPtr} {block : BlockPtr}

include hLowerable in
/-- Only a branch has a successor. -/
theorem isGmirBranch (opIn : op.InBounds ctx.raw) (hMem : block ∈ op.getSuccessors! ctx.raw) :
    op.IsGmirBranch ctx.raw := by
  apply Classical.byContradiction
  intro hNot
  have hEmpty : op.getSuccessors! ctx.raw = #[] := by
    apply Array.eq_empty_of_size_eq_zero
    rw [OperationPtr.getSuccessors!.size_eq_getNumSuccessors!]
    exact hLowerable.successors op opIn hNot
  simp [hEmpty] at hMem

include hLowerable in
/-- A block that a branch targets is among the blocks that the pass may convert. -/
theorem mem_convertible (opIn : op.InBounds ctx.raw) (hBranch : op.IsGmirBranch ctx.raw)
    (hMem : block ∈ op.getSuccessors! ctx.raw) :
    block ∈ ctx.raw.blocks.keys.filter
      fun block => !(Std.HashSet.ofList (blockedTargets ctx)).contains block &&
        isConvertible ctx block && block.hasPredecessor! ctx.raw := by
  have blockIn := OperationPtr.getSuccessors!_inBounds opIn hMem
  have hUsed : block.hasPredecessor! ctx.raw :=
    (BlockPtr.hasPredecessor_iff_successor blockIn).mpr ⟨op, opIn, hMem⟩
  have hNotBlocked : block ∉ blockedTargets ctx := by
    intro hBlocked
    obtain ⟨o, hO, hTarget⟩ := List.mem_flatMap.mp hBlocked
    split at hTarget
    · simp at hTarget
    next hNotLowered =>
      have oIn : o.InBounds ctx.raw := OperationPtr.inBounds_def.mpr (Std.HashMap.mem_keys.mp hO)
      have hB := hLowerable.isGmirBranch oIn (by simpa using hTarget)
      rcases hB with hB | hB <;> simp [isLoweredBranch, hB] at hNotLowered
  have hConvertible : isConvertible ctx block := by
    simp only [isConvertible, List.all_eq_true, List.mem_range]
    intro i hi
    exact fitsRegister_of_roundTrips (by
      simpa [BlockPtr.getArgument_def] using hLowerable.arguments op block i opIn hBranch hMem hi)
  refine List.mem_filter.mpr ⟨Std.HashMap.mem_keys.mpr (BlockPtr.inBounds_def.mp blockIn), ?_⟩
  simp [Std.HashSet.contains_ofList, hNotBlocked, hConvertible, hUsed]

end BranchesLowerable

/-- Nothing is dropped when the pass lowers every branch. -/
theorem dropTargetsOfUnlowered_eq_self {ctx : WfIRContext OpCode} {ops : List OperationPtr}
    {convertible : List BlockPtr}
    (h : ∀ op ∈ ops, op.IsGmirBranch ctx.raw →
      ∀ block ∈ op.getSuccessors! ctx.raw, block ∈ convertible) :
    ∀ fuel, dropTargetsOfUnlowered ctx ops fuel convertible = convertible
  | 0 => rfl
  | fuel + 1 => by
    simp only [dropTargetsOfUnlowered, Std.HashSet.contains_ofList]
    split
    next hAny =>
      exfalso
      obtain ⟨block, hMem, -⟩ := List.any_eq_true.mp hAny
      obtain ⟨op, hOp, hTarget⟩ := List.mem_flatMap.mp hMem
      split at hTarget
      next hCond =>
        simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true,
          decide_eq_true_eq] at hCond
        obtain ⟨hBranch, hAll⟩ := hCond
        obtain ⟨b, hb, hNot⟩ := List.all_eq_false.mp hAll
        exact hNot (by simpa using h op hOp hBranch b (by simpa using hb))
      next => simp at hTarget
    next => rfl

/-! ## The two phases give a branch lowering -/

section assemble

variable {ctx₀ ctxA ctx' : WfIRContext OpCode} {doneOps : List OperationPtr}
  {compareOf : OperationPtr → Option Compare}
  {regOp : OperationPtr → Nat → OperationPtr} {newBranch : OperationPtr → OperationPtr}
  {blocks : List BlockPtr} {doneArgs : List BlockArgumentPtr}
  {argCast : BlockArgumentPtr → OperationPtr}

/-- An argument is converted exactly when its block is. -/
theorem PhaseBlocks.mem_done_iff (hB : PhaseBlocks ctxA ctx' blocks doneArgs argCast)
    {arg : BlockArgumentPtr} (argIn : arg.InBounds ctxA.raw) :
    arg ∈ doneArgs ↔ arg.block ∈ blocks := by
  have hFilter := hB.argsOf arg.block
  have hMem : arg ∈ doneArgs ↔ arg ∈ doneArgs.filter (·.block = arg.block) := by
    simp [List.mem_filter]
  rw [hMem, hFilter]
  split
  next hIn =>
    simp only [hIn, iff_true, blockArgs, List.mem_map, List.mem_range]
    obtain ⟨_, hIndex⟩ := BlockArgumentPtr.inBounds_def.mp argIn
    exact ⟨arg.index, by grind, rfl⟩
  next hNotIn => simp [hNotIn]

/-- On the values of the source, the two ways to say what stands for a value agree. -/
theorem PhaseBlocks.lowerArgs_eq (hB : PhaseBlocks ctxA ctx' blocks doneArgs argCast)
    {value : ValuePtr} (valueIn : value.InBounds ctxA.raw) :
    lowerArgs doneArgs argCast value = lowerValue (fun b => decide (b ∈ blocks)) argCast value := by
  rcases value with r | arg
  · rfl
  · simp [lowerArgs, lowerValue, hB.mem_done_iff (by simpa using valueIn)]

/-- The `g_icmp` whose result the operand `0` of `op` is. -/
@[expose]
def icmpOfBranch (ctx : IRContext OpCode) (op : OperationPtr) : OperationPtr :=
  match op.getOperand! ctx 0 with
  | .opResult r => r.op
  | .blockArgument _ => default

/-- What `matchCompare` finds, in terms of `icmpOfBranch`. -/
theorem matchCompare_spec' {ctx : WfIRContext OpCode} {op : OperationPtr} {c : Compare}
    (opIn : op.InBounds ctx.raw) (h : matchCompare ctx.raw op = some c) :
    let icmp := icmpOfBranch ctx.raw op
    op.getOpType! ctx.raw = .gmir .g_brcond ∧
      icmp.InBounds ctx.raw ∧ icmp.getOpType! ctx.raw = .gmir .g_icmp ∧
      icmp.getNumResults! ctx.raw = 1 ∧ op.getOperand! ctx.raw 0 = icmp.getResult 0 ∧
      icmp.getNumOperands! ctx.raw = 2 ∧
      icmp.getOperand! ctx.raw 0 ≠ icmp.getResult 0 ∧
      icmp.getOperand! ctx.raw 1 ≠ icmp.getResult 0 ∧
      fillsRegister ((icmp.getOperand! ctx.raw 0).getType! ctx.raw) ∧
      compareBranch (icmp.getProperties! ctx.raw (OpCode.gmir .g_icmp)).predicate
        (icmp.getOperand! ctx.raw 0) (icmp.getOperand! ctx.raw 1)
        (matchGConstantIntVal (icmp.getOperand! ctx.raw 1) ctx.raw) = c ∧
      op.getPrevOp! ctx.raw = some icmp := by
  obtain ⟨icmp, hType, hCond, hPrev, hIcmpType, hNumOps, hNumRes, hLhs, hRhs, hFills, hEq⟩ :=
    matchCompare_spec opIn h
  have hIcmp : icmpOfBranch ctx.raw op = icmp := by
    simp [icmpOfBranch, hCond, OperationPtr.getResult_def]
  have icmpIn : icmp.InBounds ctx.raw := by
    have := OperationPtr.prev!_inBounds ctx.wellFormed.inBounds opIn
    rw [hPrev] at this
    simpa using this
  simp only [hIcmp]
  exact ⟨hType, icmpIn, hIcmpType, hNumRes, hCond, hNumOps, hLhs, hRhs, hFills, hEq, hPrev⟩

/-- A value whose register is in front of a lowered branch is a value of the module. -/
theorem regOperands_inBounds {ctx : WfIRContext OpCode} {op : OperationPtr}
    {compareOf : OperationPtr → Option Compare} (opIn : op.InBounds ctx.raw)
    (hCompare : compareOf op = matchCompare ctx.raw op) {i : Nat} {value : ValuePtr}
    (h : (regOperands ctx.raw op (compareOf op))[i]? = some (some value)) :
    value.InBounds ctx.raw := by
  have operandIn : ∀ j, j < op.getNumOperands! ctx.raw →
      (op.getOperand! ctx.raw j).InBounds ctx.raw := fun j hj =>
    OperationPtr.getOperands!_inBounds ctx.wellFormed.inBounds opIn
      (OperationPtr.getOperands!.mem_getOperand hj)
  rcases hc : compareOf op with _ | ⟨branch, l, r⟩
  · rw [hc, regOperands_none] at h
    obtain ⟨hi, rfl⟩ : i < op.getNumOperands! ctx.raw ∧ op.getOperand! ctx.raw i = value := by
      grind [List.getElem?_range]
    exact operandIn i hi
  · obtain ⟨-, icmpIn, -, -, -, hNumOps, -, -, -, hEq, -⟩ :=
      matchCompare_spec' opIn (hCompare ▸ hc)
    have icmpOperandIn : ∀ j, j < 2 →
        ((icmpOfBranch ctx.raw op).getOperand! ctx.raw j).InBounds ctx.raw := fun j hj =>
      OperationPtr.getOperands!_inBounds ctx.wellFormed.inBounds icmpIn
        (OperationPtr.getOperands!.mem_getOperand (by omega))
    have hCompared : some value = l ∨ some value = r → value.InBounds ctx.raw := by
      intro hMem
      have := compareBranch_operands (value := some value) (by rw [hEq]; exact hMem)
      rcases this with h | h | h
      · simp at h
      · obtain rfl := Option.some.inj h; exact icmpOperandIn 0 (by omega)
      · obtain rfl := Option.some.inj h; exact icmpOperandIn 1 (by omega)
    rw [hc, regOperands_some] at h
    rcases i with _ | _ | i
    · exact hCompared (.inl (by simpa using h.symm))
    · exact hCompared (.inr (by simpa using h.symm))
    · obtain ⟨hi, rfl⟩ : i + 1 < op.getNumOperands! ctx.raw ∧
          op.getOperand! ctx.raw (i + 1) = value := by
        simp only [List.getElem?_cons_succ] at h
        grind [List.getElem?_range]
      exact operandIn _ hi

/-- The module after both phases is the branch lowering of the module before them. -/
def BranchLowering.ofPhases (hA : PhaseA ctx₀ ctxA doneOps compareOf regOp newBranch)
    (hDone : ∀ o : OperationPtr, o.InBounds ctx₀.raw → o ∈ doneOps)
    (hB : PhaseBlocks ctxA ctx' blocks doneArgs argCast)
    (hTargets : ∀ (op : OperationPtr) (block : BlockPtr), op.InBounds ctx₀.raw →
      op.IsGmirBranch ctx₀.raw → block ∈ op.getSuccessors! ctx₀.raw → block ∈ blocks)
    (hBranchedTo : ∀ block ∈ blocks, ∃ op : OperationPtr, op.InBounds ctx₀.raw ∧
      block ∈ op.getSuccessors! ctx₀.raw)
    (hCompare : ∀ o : OperationPtr, o.InBounds ctx₀.raw → compareOf o = matchCompare ctx₀.raw o)
    {root : OperationPtr} (hVerified : ctx₀.Verified root)
    (hLowerable : BranchesLowerable ctx₀) :
    BranchLowering ctx₀ ctx' where
  converted := fun block => decide (block ∈ blocks)
  argCast := argCast
  compare := compareOf
  icmpOf := icmpOfBranch ctx₀.raw
  constantOf := fun op =>
    matchGConstantIntVal ((icmpOfBranch ctx₀.raw op).getOperand! ctx₀.raw 1) ctx₀.raw
  regOp := regOp
  newBranch := newBranch
  blockIn := fun h => hB.phase.ctxSame.blockIn (hA.ctxSame.blockIn h)
  numArguments := fun h =>
    (hB.phase.ctxSame.numArguments (hA.ctxSame.blockIn h)).trans (hA.ctxSame.numArguments h)
  operationList := fun {block} hBlock => by
    have blockInA := hA.ctxSame.blockIn hBlock
    change block.opList ctx' _ = _
    rw [hB.phase.opList block blockInA, hB.argsOf block, hA.opList block hBlock]
    congr 1
    · by_cases hMem : block ∈ blocks
      · simp [hMem, blockArgs, hA.ctxSame.numArguments hBlock, BlockPtr.getArgument_def]
      · simp [hMem]
    · apply List.flatMap_congr_of_mem
      intro o ho
      have oIn : o.InBounds ctx₀.raw := by
        have := BlockPtr.operationListWF ctx₀.raw block hBlock ctx₀.wellFormed
        exact this.arrayInBounds (by simpa using ho)
      simp [lowerOp, loweredOps, hDone o oIn]
  regionIn := fun h => hB.phase.ctxSame.regionIn (hA.ctxSame.regionIn h)
  firstBlock := fun h =>
    (hB.phase.ctxSame.firstBlock (hA.ctxSame.regionIn h)).trans (hA.ctxSame.firstBlock h)
  entryNotConverted := fun {region block} regionIn hFirst => by
    apply Classical.byContradiction
    intro hConverted
    /- A converted block is branched to, which the verifier forbids for an entry block. -/
    obtain ⟨op, opIn, hSuccessor⟩ := hBranchedTo block (by simpa using hConverted)
    have blockIn := OperationPtr.getSuccessors!_inBounds opIn hSuccessor
    have := (BlockPtr.hasPredecessor_iff_successor blockIn).mpr ⟨op, opIn, hSuccessor⟩
    rw [hVerified.entryBlock_hasNoPredecessor blockIn
      (RegionPtr.parent_of_firstBlock regionIn hFirst) hFirst] at this
    simp at this
  argTypeConverted := fun {block i} blockIn hConverted hi => by
    have hMem : block ∈ blocks := by simpa using hConverted
    have argIn₀ : (ValuePtr.blockArgument (block.getArgument i)).InBounds ctx₀.raw := by
      simp only [ValuePtr.inBounds_blockArg, BlockPtr.getArgument_def]
      exact BlockArgumentPtr.inBounds_def.mpr ⟨blockIn, by grind⟩
    have hTypeA := hA.types _ argIn₀
    have hDoneArg : block.getArgument i ∈ doneArgs :=
      (hB.mem_done_iff (by simpa using hTypeA.1)).mpr (by simpa [BlockPtr.getArgument_def] using hMem)
    have hTypeB := (hB.phase.types _ hTypeA.1).2
    simp only [show (∃ arg ∈ doneArgs, ValuePtr.blockArgument (block.getArgument i) =
      .blockArgument arg) from ⟨_, hDoneArg, rfl⟩, ↓reduceIte] at hTypeB
    obtain ⟨op, opIn, hSuccessor⟩ := hBranchedTo block hMem
    exact ⟨hTypeB, hLowerable.arguments op block i opIn (hLowerable.isGmirBranch opIn hSuccessor)
      hSuccessor hi⟩
  argTypeOther := fun {block i} blockIn hConverted hi => by
    have hNotMem : block ∉ blocks := by simpa using hConverted
    have argIn₀ : (ValuePtr.blockArgument (block.getArgument i)).InBounds ctx₀.raw := by
      simp only [ValuePtr.inBounds_blockArg, BlockPtr.getArgument_def]
      exact BlockArgumentPtr.inBounds_def.mpr ⟨blockIn, by grind⟩
    have hTypeA := hA.types _ argIn₀
    have hTypeB := (hB.phase.types _ hTypeA.1).2
    have hNo : ¬ ∃ arg ∈ doneArgs, ValuePtr.blockArgument (block.getArgument i) =
        .blockArgument arg := by
      rintro ⟨arg, hArg, hEq⟩
      simp only [ValuePtr.blockArgument.injEq] at hEq
      subst hEq
      exact hNotMem (by
        simpa [BlockPtr.getArgument_def] using
          (hB.mem_done_iff (by simpa using hTypeA.1)).mp hArg)
    simp only [hNo, ↓reduceIte] at hTypeB
    exact hTypeB.trans hTypeA.2
  argCastSpec := fun {arg} argIn hConverted => by
    have hMem : arg.block ∈ blocks := by simpa using hConverted
    have hTypeA := hA.types (.blockArgument arg) (by simpa using argIn)
    have hDoneArg : arg ∈ doneArgs := (hB.mem_done_iff (by simpa using hTypeA.1)).mpr hMem
    obtain ⟨_, c₂, c₃, c₄, c₅, c₆⟩ := hB.phase.args arg hDoneArg
    refine ⟨c₂, fun result resultIn hEq => ?_, c₄, hTypeA.2 ▸ c₅, c₆⟩
    obtain ⟨opIn, hIndex⟩ := OpResultPtr.inBounds_def.mp resultIn
    have hNotLowered : ¬ (result.op ∈ doneOps ∧ result.op.IsGmirBranch ctx₀.raw) := fun h => by
      have := (hA.branch result.op h.1 h.2).numResults
      grind
    exact c₃ (hEq ▸ (hA.ops result.op opIn hNotLowered).inBounds)
  argCastInj := fun {arg₁ arg₂} in₁ in₂ h₁ h₂ hEq => by
    have m₁ := (hB.mem_done_iff (by simpa using (hA.types (.blockArgument arg₁)
      (by simpa using in₁)).1)).mpr (by simpa using h₁)
    have m₂ := (hB.mem_done_iff (by simpa using (hA.types (.blockArgument arg₂)
      (by simpa using in₂)).1)).mpr (by simpa using h₂)
    exact hB.phase.inj arg₁ m₁ arg₂ m₂ hEq
  opSpec := fun {op} opIn hBranch => by
    have sA := hA.ops op opIn (fun h => hBranch h.2)
    have sB := hB.phase.ops op sA.inBounds
    refine ⟨sB.inBounds, sB.opType.trans sA.opType,
      fun c => (sB.properties c).trans (sA.properties c),
      sB.resultTypes.trans sA.resultTypes, ?_, sB.numRegions.trans sA.numRegions,
      (sB.region 0).trans (sA.region 0),
      (sB.getParentOp! hB.phase.ctxSame sA.inBounds).trans (sA.getParentOp! hA.ctxSame opIn)⟩
    rw [sB.operands, sA.operands, Array.map_map]
    apply Array.map_congr_left
    intro value hValue
    have valueIn := OperationPtr.getOperands!_inBounds ctx₀.wellFormed.inBounds opIn hValue
    simpa using hB.lowerArgs_eq (hA.types value valueIn).1
  opSuccessors := fun {op} opIn hBranch => by
    have sA := hA.ops op opIn (fun h => hBranch h.2)
    have sB := hB.phase.ops op sA.inBounds
    have hEmpty : op.getSuccessors! ctx₀.raw = #[] := by
      apply Array.eq_empty_of_size_eq_zero
      rw [OperationPtr.getSuccessors!.size_eq_getNumSuccessors!]
      exact hA.other op (hDone op opIn) hBranch
    exact ⟨hEmpty, by rw [sB.successors, sA.successors, hEmpty]⟩
  branchNumResults := fun opIn hBranch => (hA.branch _ (hDone _ opIn) hBranch).numResults
  branchSuccessorConverted := fun opIn hBranch hMem => by
    simpa using hTargets _ _ opIn hBranch hMem
  operandRoundTrips := fun {op i} opIn hBranch hi => hLowerable.operands op i opIn hBranch hi
  regOpSpec := fun {op i} opIn hBranch hi => by
    have hFacts := hA.branch op (hDone op opIn) hBranch
    obtain ⟨c₁, c₂, -⟩ := hFacts.regOpSpec i hi
    have sB := hB.phase.ops (regOp op i) c₁
    refine ⟨sB.inBounds, c₂, fun arg argIn hConverted hEq => ?_⟩
    have hDoneArg : arg ∈ doneArgs := (hB.mem_done_iff (by
      simpa using (hA.types (.blockArgument arg) (by simpa using argIn)).1)).mpr
      (by simpa using hConverted)
    exact (hB.phase.args arg hDoneArg).2.2.1 (hEq ▸ c₁)
  regOpCast := fun {op i value} opIn hBranch hSource => by
    have hFacts := hA.branch op (hDone op opIn) hBranch
    have hi : i < (regOperands ctx₀.raw op (compareOf op)).length :=
      (List.getElem?_eq_some_iff.mp hSource).1
    obtain ⟨c₁, -, c₃⟩ := hFacts.regOpSpec i hi
    rw [hSource] at c₃
    have hIs := c₃.of_opSame (hB.phase.ops (regOp op i) c₁)
    simp only [Option.join_some, Option.map_some, RegOpIs] at hIs
    obtain ⟨h₁, h₂, h₃⟩ := hIs
    refine ⟨h₁, h₂, by rw [h₃]; simpa using hB.lowerArgs_eq (hA.types value
      (regOperands_inBounds opIn (hCompare op opIn) hSource)).1⟩
  regOpX0 := fun {op i} opIn hBranch hSource => by
    have hFacts := hA.branch op (hDone op opIn) hBranch
    have hi : i < (regOperands ctx₀.raw op (compareOf op)).length :=
      (List.getElem?_eq_some_iff.mp hSource).1
    obtain ⟨c₁, -, c₃⟩ := hFacts.regOpSpec i hi
    rw [hSource] at c₃
    have hIs := c₃.of_opSame (hB.phase.ops (regOp op i) c₁)
    simpa [RegOpIs] using hIs
  regOpInj := fun opIn hBranch hi hj hEq =>
    (hA.branch _ (hDone _ opIn) hBranch).regOpInj _ _ hi hj hEq
  newBranchSpec := fun {op} opIn hBranch => by
    have hFacts := hA.branch op (hDone op opIn) hBranch
    have sB := hB.phase.ops (newBranch op) hFacts.newIn
    refine ⟨sB.inBounds, ?_, sB.successors.trans hFacts.newSuccessors, ?_⟩
    · rw [← OperationPtr.getResultTypes!.size_eq_getNumResults!, sB.resultTypes,
        hFacts.newResultTypes]
      rfl
    · rw [sB.operands, hFacts.newOperands, Array.map_map]
      apply Array.map_congr_left
      intro i _
      simp [lowerArgs, OperationPtr.getResult_def]
  newBranchBr := fun {op} opIn hType => by
    have hFacts := hA.branch op (hDone op opIn) (.inl hType)
    refine ⟨?_, (hB.phase.ops (newBranch op) hFacts.newIn).opType.trans (hFacts.newBr hType)⟩
    rcases hc : compareOf op with _ | c
    · rfl
    · have := (matchCompare_spec' opIn ((hCompare op opIn) ▸ hc)).1
      rw [hType] at this
      simp at this
  newBranchBnez := fun {op} opIn hType hc => by
    have hFacts := hA.branch op (hDone op opIn) (.inr hType)
    have sB := hB.phase.ops (newBranch op) hFacts.newIn
    exact ⟨sB.opType.trans (hFacts.newBnez hType hc).1,
      by rw [sB.properties]; exact (hFacts.newBnez hType hc).2⟩
  newBranchCompare := fun {op branch l r} opIn hc => by
    have hType := (matchCompare_spec' opIn ((hCompare op opIn) ▸ hc)).1
    have hFacts := hA.branch op (hDone op opIn) (.inr hType)
    have sB := hB.phase.ops (newBranch op) hFacts.newIn
    refine ⟨sB.opType.trans (hFacts.newCompare hType branch l r hc).1, _,
      by rw [sB.properties]; exact (hFacts.newCompare hType branch l r hc).2, rfl⟩
  compareSpec := fun {op c} opIn hc => by
    obtain ⟨hType, icmpIn, hIcmpType, hNumRes, hCond, hNumOps, hLhs, hRhs, hFills, hEq, -⟩ :=
      matchCompare_spec' opIn ((hCompare op opIn) ▸ hc)
    exact ⟨hType, icmpIn, hIcmpType, hNumRes, hCond, hNumOps, hLhs, hRhs, hFills, hEq⟩
  constantSpec := fun {op c k} opIn hc hk => by
    obtain ⟨-, icmpIn, -, -, -, hNumOps, -⟩ := matchCompare_spec' opIn ((hCompare op opIn) ▸ hc)
    exact matchGConstantIntVal_spec (OperationPtr.getOperands!_inBounds ctx₀.wellFormed.inBounds
      icmpIn (OperationPtr.getOperands!.mem_getOperand (by omega))) hk
  compareAdjacent := fun {op c block} blockIn {pre post} opIn hc hList => by
    have hPrev := (matchCompare_spec' opIn ((hCompare op opIn) ▸ hc)).2.2.2.2.2.2.2.2.2.2
    exact getLast?_of_getPrevOp! blockIn hList hPrev

end assemble

/-! ## The pass -/

/-- A module that `convertModule` returns is the branch lowering of its input. -/
theorem convertModule_branchLowering {ctx ctx' : WfIRContext OpCode} {root : OperationPtr}
    (hVerified : ctx.Verified root)
    (hNoUnreachable : ∀ o : OperationPtr, o.InBounds ctx.raw →
      o.getOpType! ctx.raw ≠ OpCode.llvm .unreachable)
    (hLowerable : BranchesLowerable ctx)
    (h : convertModule ctx = .ok ctx') :
    Nonempty (BranchLowering ctx ctx') := by
  have hKeys : ∀ o : OperationPtr, o ∈ ctx.raw.operations.keys ↔ o.InBounds ctx.raw := fun o => by
    rw [Std.HashMap.mem_keys, OperationPtr.inBounds_def]
  have hNodup : ctx.raw.operations.keys.Nodup := by
    have := ctx.raw.operations.distinct_keys
    simpa [List.Nodup] using this
  /- Every branch is lowered, so no block is dropped and every target is converted. -/
  have hConvertible : ∀ op ∈ ctx.raw.operations.keys, op.IsGmirBranch ctx.raw →
      ∀ block ∈ op.getSuccessors! ctx.raw, block ∈ ctx.raw.blocks.keys.filter
        fun block => !(Std.HashSet.ofList (blockedTargets ctx)).contains block &&
          isConvertible ctx block && block.hasPredecessor! ctx.raw :=
    fun op hOp hBranch _ hMem => hLowerable.mem_convertible ((hKeys op).mp hOp) hBranch hMem
  simp only [convertModule, bind, Except.bind,
    dropTargetsOfUnlowered_eq_self hConvertible] at h
  split at h
  next => simp at h
  next ctxA hLower =>
    obtain ⟨doneOps, regOp, newBranch, hA, hDoneOps⟩ :=
      (PhaseA.init (regOp := fun _ _ => default) (newBranch := fun _ => default)).foldlM
        (fun o ho => (hKeys o).mp ho) hNodup (fun _ _ h => by simp at h)
        (fun o ho => hNoUnreachable o ((hKeys o).mp ho))
        (fun o ho => hLowerable.successors o ((hKeys o).mp ho))
        (fun o ho hBranch => Array.all_eq_true_iff_forall_mem.mpr fun block hMem => by
          simpa [Std.HashSet.contains_ofList] using hConvertible o ho hBranch block hMem)
        (fun o ho hBranch =>
          OperationPtr.Verified.gmir_branch
            (OperationPtr.satisfyInvariants_of_IRContext_satisfyOpInvariants hVerified
              ((hKeys o).mp ho)) hBranch)
        hLower
    /- Every block the pass converts is a block of the module that has a predecessor. -/
    have hUsed : ∀ block ∈ ctx.raw.blocks.keys.filter
        (fun block => !(Std.HashSet.ofList (blockedTargets ctx)).contains block &&
          isConvertible ctx block && block.hasPredecessor! ctx.raw),
        block.InBounds ctx.raw ∧ block.hasPredecessor! ctx.raw := by
      intro block hBlock
      obtain ⟨hKey, hFilter⟩ := List.mem_filter.mp hBlock
      refine ⟨BlockPtr.inBounds_def.mpr (Std.HashMap.mem_keys.mp hKey), ?_⟩
      simp only [Bool.and_eq_true] at hFilter
      exact hFilter.2
    obtain ⟨blocks, doneArgs, argCast, hB, hBlocks⟩ :=
      (PhaseBlocks.foldlM (blocks := []) (argCast := fun _ => default)
        ⟨PhaseB.init, fun _ h => by simp at h, fun _ => by simp⟩
        (fun block hBlock => hA.ctxSame.blockIn (hUsed block hBlock).1)
        (List.filter_sublist.nodup (by
          simpa [List.Nodup] using ctx.raw.blocks.distinct_keys))
        (fun _ _ => by simp) h)
    refine ⟨BranchLowering.ofPhases hA (fun o oIn => (hDoneOps o).mpr (.inl ((hKeys o).mpr oIn)))
      hB (fun op block opIn hBranch hMem =>
        (hBlocks block).mpr (.inl (hConvertible op ((hKeys op).mpr opIn) hBranch block hMem)))
      (fun block hBlock => ?_) (fun o oIn => getElem?_ofList_matchCompare hNodup ((hKeys o).mpr oIn))
      hVerified hLowerable⟩
    rcases (hBlocks block).mp hBlock with hConv | hNil
    · exact (BlockPtr.hasPredecessor_iff_successor (hUsed block hConv).1).mp
        (hUsed block hConv).2
    · simp at hNil

/--
  The RISC-V branch lowering refines a module that verifies, holds no
  `llvm.unreachable`, and whose branches it lowers all of: every function of the
  input is refined by the function of the same name in the module the pass
  returns.

  The lowering also replaces an `llvm.unreachable` by `riscv_cf.unreachable`,
  which this proof does not cover: an operation that is neither left alone nor
  lowered as a branch is a shape `PhaseA` does not describe. Nor does it cover a
  module in which the pass leaves a branch alone, or passes a pointer through a
  register, which `BranchesLowerable` rules out.
-/
theorem convertModule_isModuleRefinedBy {ctx ctx' : WfIRContext OpCode} {root : OperationPtr}
    (hVerified : ctx.Verified root)
    (hNoUnreachable : ∀ o : OperationPtr, o.InBounds ctx.raw →
      o.getOpType! ctx.raw ≠ OpCode.llvm .unreachable)
    (hLowerable : BranchesLowerable ctx) (hMono : MonotoneOps ctx)
    (h : convertModule ctx = .ok ctx') (module : OperationPtr) :
    module.isModuleRefinedBy ctx module ctx' :=
  (convertModule_branchLowering hVerified hNoUnreachable hLowerable h).elim fun lowering =>
    lowering.isModuleRefinedBy hMono module

end Veir
