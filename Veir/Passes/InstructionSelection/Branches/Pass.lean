module

public import Veir.Passes.InstructionSelection.Branches.Frame
public import Veir.Passes.InstructionSelection.Branches.Simulation

import all Veir.Passes.InstructionSelection.RISCV64Branches

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

end Veir
