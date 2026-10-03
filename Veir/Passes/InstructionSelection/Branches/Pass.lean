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
    fitsRegister (operand.getType! ctx.raw) ∧
    ∃ cast, casts' = casts.push cast ∧
      WfRewriter.createOp! ctx Builtin.unrealized_conversion_cast #[RegisterType.mk] #[operand] #[]
        #[] default (some ip) = some (ctx', cast) := by
  simp only [castToReg] at h
  split at h
  next => simp [throw, throwThe, MonadExceptOf.throw] at h
  next hFits =>
    split at h
    next ctx₁ cast hCreate =>
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by simpa using hFits, cast, rfl, hCreate⟩
    next => simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ## Casting the operands of a branch -/

/--
  The module while the operands of the branch `op` are cast: `casts` are the
  casts of `values`, in front of `op`, and nothing else changed since `ctx₀`.
-/
structure CastsInv (ctx₀ : WfIRContext OpCode) (op : OperationPtr) (values : List ValuePtr)
    (ctx : WfIRContext OpCode) (casts : Array OperationPtr) : Prop where
  ops : ∀ o, o.InBounds ctx₀.raw → OpSame id ctx₀.raw ctx.raw o
  ctxSame : CtxSame ctx₀.raw ctx.raw
  types : ∀ value : ValuePtr, value.InBounds ctx₀.raw →
    value.InBounds ctx.raw ∧ value.getType! ctx.raw = value.getType! ctx₀.raw
  size : casts.size = values.length
  cast : ∀ i (hi : i < casts.size) (hi' : i < values.length),
    casts[i].InBounds ctx.raw ∧ ¬ casts[i].InBounds ctx₀.raw ∧
    casts[i].getOpType! ctx.raw = .builtin .unrealized_conversion_cast ∧
    casts[i].getResultTypes! ctx.raw = #[(RegisterType.mk : TypeAttr)] ∧
    casts[i].getOperands! ctx.raw = #[values[i]] ∧
    fitsRegister (values[i].getType! ctx₀.raw)
  nodup : casts.toList.Nodup
  opList : ∀ (block : BlockPtr) (blockIn : block.InBounds ctx₀.raw),
    block.opList ctx (ctxSame.blockIn blockIn) =
      (block.opList ctx₀ blockIn).replaceBy op (casts.toList ++ [op])

theorem CastsInv.step {ctx₀ ctx ctx' : WfIRContext OpCode} {op : OperationPtr}
    {values : List ValuePtr} {casts casts' : Array OperationPtr} {value : ValuePtr}
    (hInv : CastsInv ctx₀ op values ctx casts) (opIn : op.InBounds ctx₀.raw)
    (valueIn : value.InBounds ctx₀.raw)
    (h : castToReg (.before op) (ctx, casts) value = .ok (ctx', casts')) :
    CastsInv ctx₀ op (values ++ [value]) ctx' casts' := by
  obtain ⟨hFits, cast, rfl, hCreate⟩ := castToReg_ok h
  obtain ⟨h₁, h₂, h₃, h₄, hCreate⟩ := WfRewriter.createOp_of_createOp! hCreate
  obtain ⟨hNotIn, hIn, hOps, hCtx, hTypes, hType, hResultTypes, hOperands, _⟩ :=
    WfRewriter.createOp_frame hCreate
  have hMono : ∀ ptr : GenericPtr, ptr.InBounds ctx.raw → ptr.InBounds ctx'.raw :=
    fun ptr => WfRewriter.createOp_inBounds_mono hCreate
  have hOld : ∀ i (hi : i < casts.size), casts[i] ≠ cast := fun i hi hEq =>
    hNotIn (hEq ▸ (hInv.cast i hi (by rw [← hInv.size]; exact hi)).1)
  refine ⟨fun o oIn => (hInv.ops o oIn).trans_id (hOps o (hInv.ops o oIn).inBounds),
    hInv.ctxSame.trans hCtx, fun v vIn => ?_, by simp [hInv.size], fun i hi hi' => ?_, ?_,
    fun block blockIn => ?_⟩
  · have := hInv.types v vIn
    exact ⟨by simpa using hMono (.value v) (by simpa using this.1),
      (hTypes v this.1).trans this.2⟩
  · by_cases hLt : i < casts.size
    · obtain ⟨c₁, c₂, c₃, c₄, c₅, c₆⟩ := hInv.cast i hLt (by rw [← hInv.size]; exact hLt)
      have hSame := hOps casts[i] c₁
      simp only [Array.getElem_push_lt hLt, List.getElem_append_left (hInv.size ▸ hLt)]
      exact ⟨hSame.inBounds, c₂, hSame.opType.trans c₃, hSame.resultTypes.trans c₄,
        by rw [hSame.operands, c₅]; simp, c₆⟩
    · have hEq : i = casts.size := by simp at hi; omega
      subst hEq
      have hNotIn₀ : ¬ cast.InBounds ctx₀.raw := fun h => hNotIn (hInv.ops cast h).inBounds
      simp only [Array.getElem_push_eq]
      simp only [hInv.size, List.getElem_concat_length]
      refine ⟨hIn, hNotIn₀, hType.trans ofDialect_cast, hResultTypes, hOperands, ?_⟩
      rw [← (hInv.types value valueIn).2]; exact hFits
  · rw [Array.toList_push, List.nodup_append]
    refine ⟨hInv.nodup, by simp, fun a ha b hb => ?_⟩
    obtain rfl : b = cast := by simpa using hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    exact hOld i (by simpa using hi)
  · have hNotMem : op ∉ casts.toList := fun hMem => by
      obtain ⟨i, hi, hEq⟩ := List.getElem_of_mem hMem
      have hi' : i < casts.size := by simpa using hi
      have hEq' : casts[i] = op := by simpa using hEq
      exact (hInv.cast i hi' (by rw [← hInv.size]; exact hi')).2.1 (hEq' ▸ opIn)
    rw [WfRewriter.createOp_before_opList hCreate (hInv.ctxSame.blockIn blockIn),
      hInv.opList block blockIn, List.replaceBy_replaceBy hNotMem]
    simp

theorem CastsInv.foldlM {ctx₀ ctx ctx' : WfIRContext OpCode} {op : OperationPtr}
    {values rest : List ValuePtr} {casts casts' : Array OperationPtr}
    (hInv : CastsInv ctx₀ op values ctx casts) (opIn : op.InBounds ctx₀.raw)
    (restIn : ∀ value ∈ rest, value.InBounds ctx₀.raw)
    (h : rest.foldlM (castToReg (.before op)) (ctx, casts) = .ok (ctx', casts')) :
    CastsInv ctx₀ op (values ++ rest) ctx' casts' := by
  induction rest generalizing values ctx casts with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simpa using hInv
  | cons value rest ih =>
    simp only [List.foldlM_cons, bind, Except.bind] at h
    split at h
    next => simp at h
    next acc hStep =>
      obtain ⟨ctx₁, casts₁⟩ := acc
      have := ih (hInv.step opIn (restIn value (by simp)) hStep)
        (fun v hv => restIn v (by simp [hv])) h
      simpa using this

theorem CastsInv.init {ctx₀ : WfIRContext OpCode} {op : OperationPtr} :
    CastsInv ctx₀ op [] ctx₀ #[] :=
  ⟨fun _ oIn => OpSame.refl oIn, CtxSame.refl, fun _ vIn => ⟨vIn, rfl⟩, rfl,
    fun _ hi => by simp at hi, by simp, fun block blockIn => by
      simp [List.replaceBy_self]⟩

/-! ## Lowering one branch -/

theorem createRiscvBranch_ok {source : IRContext OpCode} {op newBranch : OperationPtr}
    {ctx ctx' : WfIRContext OpCode} {regs : Array ValuePtr}
    (h : createRiscvBranch source op ctx regs = .ok (ctx', newBranch)) :
    (op.getOpType! source = .llvm .br ∧
      WfRewriter.createOp! ctx Riscv_Cf.branch #[] regs (op.getSuccessors! source) #[] default
        (some (.before op)) = some (ctx', newBranch)) ∨
    (op.getOpType! source ≠ .llvm .br ∧
      WfRewriter.createOp! ctx Riscv_Cf.bnez #[] regs (op.getSuccessors! source) #[]
        (⟨(op.getProperties! source (OpCode.llvm .cond_br)).operandSegmentSizes⟩ :
          RISCVBrProperties)
        (some (.before op)) = some (ctx', newBranch)) := by
  simp only [createRiscvBranch] at h
  split at h
  next hType =>
    split at h
    next result hCreate =>
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact .inl ⟨hType, h ▸ hCreate⟩
    next => simp [throw, throwThe, MonadExceptOf.throw] at h
  next hType =>
    split at h
    next result hCreate =>
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact .inr ⟨hType, h ▸ hCreate⟩
    next => simp [throw, throwThe, MonadExceptOf.throw] at h

theorem eraseBranch_ok {ctx ctx' : WfIRContext OpCode} {op : OperationPtr}
    (h : eraseBranch ctx op = .ok ctx') :
    op.getNumRegions! ctx.raw = 0 ∧ op.hasUses! ctx.raw = false ∧
    ctx' = WfRewriter.eraseOp! ctx op := by
  simp only [eraseBranch] at h
  split at h
  next => simp [throw, throwThe, MonadExceptOf.throw] at h
  next hCond =>
    simp only [pure, Except.pure, Except.ok.injEq] at h
    simp only [ne_eq, Bool.or_eq_true, decide_eq_true_eq, not_or, Decidable.not_not,
      Bool.not_eq_true] at hCond
    exact ⟨hCond.1, hCond.2, h.symm⟩

/-- What lowering the branch `op` does: `casts` and `newBranch` take its place. -/
structure BranchStep (ctx ctx' : WfIRContext OpCode) (op : OperationPtr)
    (casts : Array OperationPtr) (newBranch : OperationPtr) : Prop where
  ops : ∀ o, o.InBounds ctx.raw → o ≠ op → OpSame id ctx.raw ctx'.raw o
  ctxSame : CtxSame ctx.raw ctx'.raw
  types : ∀ value : ValuePtr, value.InBounds ctx.raw → (∀ r, value = .opResult r → r.op ≠ op) →
    value.InBounds ctx'.raw ∧ value.getType! ctx'.raw = value.getType! ctx.raw
  size : casts.size = op.getNumOperands! ctx.raw
  cast : ∀ i (hi : i < casts.size),
    casts[i].InBounds ctx'.raw ∧ ¬ casts[i].InBounds ctx.raw ∧
    casts[i].getOpType! ctx'.raw = .builtin .unrealized_conversion_cast ∧
    casts[i].getResultTypes! ctx'.raw = #[(RegisterType.mk : TypeAttr)] ∧
    casts[i].getOperands! ctx'.raw = #[op.getOperand! ctx.raw i] ∧
    fitsRegister ((op.getOperand! ctx.raw i).getType! ctx.raw)
  nodup : casts.toList.Nodup
  newIn : newBranch.InBounds ctx'.raw
  newNotIn : ¬ newBranch.InBounds ctx.raw
  newNotCast : newBranch ∉ casts.toList
  newResultTypes : newBranch.getResultTypes! ctx'.raw = #[]
  newSuccessors : newBranch.getSuccessors! ctx'.raw = op.getSuccessors! ctx.raw
  newOperands : newBranch.getOperands! ctx'.raw =
    casts.map (fun cast => (cast.getResult 0 : ValuePtr))
  newBr : op.getOpType! ctx.raw = .llvm .br → newBranch.getOpType! ctx'.raw = .riscv_cf .branch
  newCondBr : op.getOpType! ctx.raw ≠ .llvm .br →
    newBranch.getOpType! ctx'.raw = .riscv_cf .bnez ∧
    (newBranch.getProperties! ctx'.raw (OpCode.riscv_cf .bnez)).operandSegmentSizes =
      (op.getProperties! ctx.raw (OpCode.llvm .cond_br)).operandSegmentSizes
  opList : ∀ (block : BlockPtr) (blockIn : block.InBounds ctx.raw),
    block.opList ctx' (ctxSame.blockIn blockIn) =
      (block.opList ctx blockIn).replaceBy op (casts.toList ++ [newBranch])

/-- The branch step from the casts, the creation of the new branch, and the erasure. -/
theorem BranchStep.of_frames {ctx ctx₁ ctx₂ ctx' : WfIRContext OpCode} {op newBranch : OperationPtr}
    {casts : Array OperationPtr} (opIn : op.InBounds ctx.raw)
    (hInv : CastsInv ctx op
      ((List.range (op.getNumOperands! ctx.raw)).map (op.getOperand! ctx.raw ·)) ctx₁ casts)
    (hNotIn : ¬ newBranch.InBounds ctx₁.raw) (hIn : newBranch.InBounds ctx₂.raw)
    (hOps : ∀ o, o.InBounds ctx₁.raw → OpSame id ctx₁.raw ctx₂.raw o)
    (hCtx : CtxSame ctx₁.raw ctx₂.raw)
    (hTypes : ∀ value : ValuePtr, value.InBounds ctx₁.raw →
      value.getType! ctx₂.raw = value.getType! ctx₁.raw)
    (hMono : ∀ ptr : GenericPtr, ptr.InBounds ctx₁.raw → ptr.InBounds ctx₂.raw)
    (hResultTypes : newBranch.getResultTypes! ctx₂.raw = #[])
    (hSuccessors : newBranch.getSuccessors! ctx₂.raw = op.getSuccessors! ctx.raw)
    (hOperands : newBranch.getOperands! ctx₂.raw =
      casts.map (fun cast => (cast.getResult 0 : ValuePtr)))
    (hBr : op.getOpType! ctx.raw = .llvm .br →
      newBranch.getOpType! ctx₂.raw = .riscv_cf .branch)
    (hCondBr : op.getOpType! ctx.raw ≠ .llvm .br →
      newBranch.getOpType! ctx₂.raw = .riscv_cf .bnez ∧
      (newBranch.getProperties! ctx₂.raw (OpCode.riscv_cf .bnez)).operandSegmentSizes =
        (op.getProperties! ctx.raw (OpCode.llvm .cond_br)).operandSegmentSizes)
    (hList : ∀ (block : BlockPtr) (blockIn : block.InBounds ctx₁.raw)
      (blockIn' : block.InBounds ctx₂.raw),
      block.opList ctx₂ blockIn' = (block.opList ctx₁ blockIn).replaceBy op [newBranch, op])
    (hErase : eraseBranch ctx₂ op = .ok ctx') :
    BranchStep ctx ctx' op casts newBranch := by
  obtain ⟨hRegions, hUses, rfl⟩ := eraseBranch_ok hErase
  have opIn₂ : op.InBounds ctx₂.raw := (hOps op (hInv.ops op opIn).inBounds).inBounds
  rw [WfRewriter.eraseOp!_eq opIn₂ hRegions (by simp [hUses])]
  obtain ⟨hOps₃, hCtx₃, hTypes₃, hValues₃⟩ := WfRewriter.eraseOp_frame (ctx := ctx₂) (op := op)
    (hRegions := hRegions) (hUses := by simp [hUses]) (opIn := opIn₂)
  have hNewNe : newBranch ≠ op := fun hEq => hNotIn (hEq ▸ (hInv.ops op opIn).inBounds)
  have hNewSame := hOps₃ newBranch hIn hNewNe
  have hSize : casts.size = op.getNumOperands! ctx.raw := by simpa using hInv.size
  have hCastNotOp : op ∉ casts.toList := fun hMem => by
    obtain ⟨i, hi, hEq⟩ := List.getElem_of_mem hMem
    have hi' : i < casts.size := by simpa using hi
    have hEq' : casts[i] = op := by simpa using hEq
    exact (hInv.cast i hi' (by simpa [hInv.size] using hi')).2.1 (hEq' ▸ opIn)
  refine {
    ops := fun o oIn hNe =>
      ((hInv.ops o oIn).trans_id (hOps o (hInv.ops o oIn).inBounds)).trans_id
        (hOps₃ o (hOps o (hInv.ops o oIn).inBounds).inBounds hNe)
    ctxSame := (hInv.ctxSame.trans hCtx).trans hCtx₃
    types := fun v vIn hv => ?_
    size := hSize
    cast := fun i hi => ?_
    nodup := hInv.nodup
    newIn := hNewSame.inBounds
    newNotIn := fun h => hNotIn (hInv.ops newBranch h).inBounds
    newNotCast := fun hMem => ?_
    newResultTypes := hNewSame.resultTypes.trans hResultTypes
    newSuccessors := hNewSame.successors.trans hSuccessors
    newOperands := by rw [hNewSame.operands, hOperands]; simp
    newBr := fun h => hNewSame.opType.trans (hBr h)
    newCondBr := fun h => ⟨hNewSame.opType.trans (hCondBr h).1,
      by rw [hNewSame.properties]; exact (hCondBr h).2⟩
    opList := fun block blockIn => ?_ }
  · have h₁ := hInv.types v vIn
    have h₂ : v.InBounds ctx₂.raw := by simpa using hMono (.value v) (by simpa using h₁.1)
    have h₃ := hValues₃ v h₂ hv
    exact ⟨h₃, (hTypes₃ v h₃).trans ((hTypes v h₁.1).trans h₁.2)⟩
  · have hi' : i < ((List.range (op.getNumOperands! ctx.raw)).map
        (op.getOperand! ctx.raw ·)).length := by simpa [hSize] using hi
    obtain ⟨c₁, c₂, c₃, c₄, c₅, c₆⟩ := hInv.cast i hi hi'
    have hNe : casts[i] ≠ op := fun hEq => c₂ (hEq ▸ opIn)
    have hSame := (hOps casts[i] c₁).trans_id (hOps₃ casts[i] (hOps casts[i] c₁).inBounds hNe)
    simp only [List.getElem_map, List.getElem_range] at c₅ c₆
    exact ⟨hSame.inBounds, c₂, hSame.opType.trans c₃, hSame.resultTypes.trans c₄,
      by rw [hSame.operands, c₅]; simp, c₆⟩
  · obtain ⟨i, hi, hEq⟩ := List.getElem_of_mem hMem
    have hi' : i < casts.size := by simpa using hi
    have hEq' : casts[i] = newBranch := by simpa using hEq
    exact hNotIn (hEq' ▸ (hInv.cast i hi' (by simpa [hInv.size] using hi')).1)
  · have blockIn₁ := hInv.ctxSame.blockIn blockIn
    have blockIn₂ := hCtx.blockIn blockIn₁
    rw [WfRewriter.eraseOp_opList blockIn₂, hList block blockIn₁ blockIn₂,
      hInv.opList block blockIn, List.replaceBy_replaceBy hCastNotOp,
      show casts.toList ++ [newBranch, op] = (casts.toList ++ [newBranch]) ++ [op] by simp,
      List.erase_replaceBy BlockPtr.opList_nodup]
    simp only [List.mem_append, List.mem_singleton, not_or]
    exact ⟨hCastNotOp, fun hEq => hNewNe hEq.symm⟩

theorem lowerBranch_spec {ctx ctx' : WfIRContext OpCode} {op : OperationPtr}
    (opIn : op.InBounds ctx.raw) (h : lowerBranch ctx op = .ok ctx') :
    ∃ casts newBranch, BranchStep ctx ctx' op casts newBranch := by
  simp only [lowerBranch, bind, Except.bind] at h
  split at h
  next => simp at h
  next acc hFold =>
    obtain ⟨ctx₁, casts⟩ := acc
    split at h
    next => simp at h
    next acc₂ hCreate =>
      obtain ⟨ctx₂, newBranch⟩ := acc₂
      simp only at h hCreate
      have hInv := CastsInv.init.foldlM opIn (fun value hValue => by
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hValue
        exact OperationPtr.getOperands!_inBounds ctx.wellFormed.inBounds opIn
          (OperationPtr.getOperands!.mem_getOperand (by simpa using hi))) hFold
      simp only [List.nil_append] at hInv
      refine ⟨casts, newBranch, ?_⟩
      rcases createRiscvBranch_ok hCreate with ⟨hType, hCreate⟩ | ⟨hType, hCreate⟩
      all_goals
        obtain ⟨h₁, h₂, h₃, h₄, hCreate⟩ := WfRewriter.createOp_of_createOp! hCreate
        obtain ⟨hNotIn, hIn, hOps, hCtx, hTypes, hNewType, hResultTypes, hOperands, hSuccessors⟩ :=
          WfRewriter.createOp_frame hCreate
        refine BranchStep.of_frames opIn hInv hNotIn hIn hOps hCtx hTypes
          (fun ptr => WfRewriter.createOp_inBounds_mono hCreate) hResultTypes hSuccessors
          hOperands ?_ ?_ (fun block blockIn blockIn' =>
            WfRewriter.createOp_before_opList hCreate blockIn blockIn') h
      · exact fun _ => hNewType.trans ofDialect_branch
      · exact fun hNe => absurd hType hNe
      · exact fun hEq => absurd hEq hType
      · exact fun _ => ⟨hNewType.trans ofDialect_bnez,
          by rw [WfRewriter.createOp_bnez_properties hCreate]⟩

/-! ## Lowering all branches -/

/-- What the lowering of the branch `op` of `ctx₀` left in `ctx`. -/
structure LoweredBranch (ctx₀ ctx : WfIRContext OpCode) (op : OperationPtr)
    (casts : Nat → OperationPtr) (newBranch : OperationPtr) : Prop where
  numResults : op.getNumResults! ctx₀.raw = 0
  cast : ∀ i, i < op.getNumOperands! ctx₀.raw →
    (casts i).InBounds ctx.raw ∧
    (∀ result : OpResultPtr, result.InBounds ctx₀.raw → result.op ≠ casts i) ∧
    (casts i).getOpType! ctx.raw = .builtin .unrealized_conversion_cast ∧
    (casts i).getResultTypes! ctx.raw = #[(RegisterType.mk : TypeAttr)] ∧
    (casts i).getOperands! ctx.raw = #[op.getOperand! ctx₀.raw i] ∧
    fitsRegister ((op.getOperand! ctx₀.raw i).getType! ctx₀.raw)
  castInj : ∀ i j, i < op.getNumOperands! ctx₀.raw → j < op.getNumOperands! ctx₀.raw →
    casts i = casts j → i = j
  newIn : newBranch.InBounds ctx.raw
  newResultTypes : newBranch.getResultTypes! ctx.raw = #[]
  newSuccessors : newBranch.getSuccessors! ctx.raw = op.getSuccessors! ctx₀.raw
  newOperands : newBranch.getOperands! ctx.raw =
    (Array.range (op.getNumOperands! ctx₀.raw)).map (fun i => ((casts i).getResult 0 : ValuePtr))
  newBr : op.getOpType! ctx₀.raw = .llvm .br → newBranch.getOpType! ctx.raw = .riscv_cf .branch
  newCondBr : op.getOpType! ctx₀.raw = .llvm .cond_br →
    newBranch.getOpType! ctx.raw = .riscv_cf .bnez ∧
    (newBranch.getProperties! ctx.raw (OpCode.riscv_cf .bnez)).operandSegmentSizes =
      (op.getProperties! ctx₀.raw (OpCode.llvm .cond_br)).operandSegmentSizes

/-- The module after the branches among `done` were lowered. -/
structure PhaseA (ctx₀ ctx : WfIRContext OpCode) (done : List OperationPtr)
    (operandCast : OperationPtr → Nat → OperationPtr) (newBranch : OperationPtr → OperationPtr) :
    Prop where
  ops : ∀ o, o.InBounds ctx₀.raw → ¬ (o ∈ done ∧ o.IsLlvmBranch ctx₀.raw) →
    OpSame id ctx₀.raw ctx.raw o
  ctxSame : CtxSame ctx₀.raw ctx.raw
  types : ∀ value : ValuePtr, value.InBounds ctx₀.raw →
    value.InBounds ctx.raw ∧ value.getType! ctx.raw = value.getType! ctx₀.raw
  other : ∀ o ∈ done, ¬ o.IsLlvmBranch ctx₀.raw → o.getNumSuccessors! ctx₀.raw = 0
  branch : ∀ o ∈ done, o.IsLlvmBranch ctx₀.raw →
    LoweredBranch ctx₀ ctx o (operandCast o) (newBranch o)
  opList : ∀ (block : BlockPtr) (blockIn : block.InBounds ctx₀.raw),
    block.opList ctx (ctxSame.blockIn blockIn) =
      (block.opList ctx₀ blockIn).flatMap fun o =>
        if o ∈ done ∧ o.IsLlvmBranch ctx₀.raw then
          (List.range (o.getNumOperands! ctx₀.raw)).map (operandCast o) ++ [newBranch o]
        else [o]

theorem PhaseA.init {ctx₀ : WfIRContext OpCode} {operandCast newBranch} :
    PhaseA ctx₀ ctx₀ [] operandCast newBranch :=
  ⟨fun _ oIn _ => OpSame.refl oIn, CtxSame.refl, fun _ vIn => ⟨vIn, rfl⟩,
    fun _ h => by simp at h, fun _ h => by simp at h, fun _ _ => by simp⟩

/--
  What `convertBranch` leaves behind, for an operation that is not an
  `llvm.unreachable`. The lowering replaces that one too, which this proof does
  not cover; `convertModule_branchLowering` assumes the module has none.
-/
theorem convertBranch_ok {ctx ctx' : WfIRContext OpCode} {op : OperationPtr}
    (hNotUnreachable : op.getOpType! ctx.raw ≠ OpCode.llvm .unreachable)
    (h : convertBranch ctx op = .ok ctx') :
    (¬ op.IsLlvmBranch ctx.raw ∧ op.getNumSuccessors! ctx.raw = 0 ∧ ctx' = ctx) ∨
    (op.IsLlvmBranch ctx.raw ∧ op.getNumResults! ctx.raw = 0 ∧ lowerBranch ctx op = .ok ctx') := by
  simp only [convertBranch] at h
  simp only [hNotUnreachable, ↓reduceIte] at h
  split at h
  next hBranch =>
    split at h
    next => simp [throw, throwThe, MonadExceptOf.throw] at h
    next hSucc =>
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact .inl ⟨hBranch, by simpa using hSucc, h.symm⟩
  next hBranch =>
    split at h
    next => simp [throw, throwThe, MonadExceptOf.throw] at h
    next hResults => exact .inr ⟨by simpa using hBranch, by simpa using hResults, h⟩

/-- An operation that stays the same stays a lowered branch's cast or new branch. -/
theorem LoweredBranch.mono {ctx₀ ctx ctx' : WfIRContext OpCode} {o : OperationPtr}
    {casts : Nat → OperationPtr} {newBranch : OperationPtr}
    (h : LoweredBranch ctx₀ ctx o casts newBranch) (hBranch : o.IsLlvmBranch ctx₀.raw)
    (hSame : ∀ o', o'.InBounds ctx.raw → ¬ o'.IsLlvmBranch ctx.raw → OpSame id ctx.raw ctx'.raw o') :
    LoweredBranch ctx₀ ctx' o casts newBranch := by
  have hNew : OpSame id ctx.raw ctx'.raw newBranch := hSame newBranch h.newIn (by
    rcases hBranch with hB | hB
    · simp [OperationPtr.IsLlvmBranch, h.newBr hB]
    · simp [OperationPtr.IsLlvmBranch, (h.newCondBr hB).1])
  have hCast : ∀ i, i < o.getNumOperands! ctx₀.raw → OpSame id ctx.raw ctx'.raw (casts i) :=
    fun i hi => hSame (casts i) (h.cast i hi).1 (by
      simp [OperationPtr.IsLlvmBranch, (h.cast i hi).2.2.1])
  refine ⟨h.numResults, fun i hi => ?_, h.castInj, hNew.inBounds,
    hNew.resultTypes.trans h.newResultTypes, hNew.successors.trans h.newSuccessors,
    by rw [hNew.operands, h.newOperands]; simp, fun hB => hNew.opType.trans (h.newBr hB),
    fun hB => ⟨hNew.opType.trans (h.newCondBr hB).1,
      by rw [hNew.properties]; exact (h.newCondBr hB).2⟩⟩
  obtain ⟨c₁, c₂, c₃, c₄, c₅, c₆⟩ := h.cast i hi
  have hS := hCast i hi
  exact ⟨hS.inBounds, c₂, hS.opType.trans c₃, hS.resultTypes.trans c₄,
    by rw [hS.operands, c₅]; simp, c₆⟩

theorem PhaseA.step_other {ctx₀ ctx : WfIRContext OpCode} {done : List OperationPtr}
    {operandCast newBranch} {op : OperationPtr}
    (hInv : PhaseA ctx₀ ctx done operandCast newBranch)
    (hBranch : ¬ op.IsLlvmBranch ctx₀.raw) (hSuccessors : op.getNumSuccessors! ctx₀.raw = 0) :
    PhaseA ctx₀ ctx (op :: done) operandCast newBranch := by
  have hIff : ∀ o, (o ∈ op :: done ∧ o.IsLlvmBranch ctx₀.raw) ↔
      (o ∈ done ∧ o.IsLlvmBranch ctx₀.raw) := by
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
    {operandCast newBranch} {op : OperationPtr} {casts : Array OperationPtr} {newOp : OperationPtr}
    (hInv : PhaseA ctx₀ ctx done operandCast newBranch)
    (opIn₀ : op.InBounds ctx₀.raw) (hNotDone : op ∉ done)
    (hBranch : op.IsLlvmBranch ctx₀.raw) (hResults : op.getNumResults! ctx₀.raw = 0)
    (hStep : BranchStep ctx ctx' op casts newOp) :
    PhaseA ctx₀ ctx' (op :: done)
      (fun o i => if o = op then casts[i]! else operandCast o i)
      (fun o => if o = op then newOp else newBranch o) := by
  have hSame := hInv.ops op opIn₀ (fun h => hNotDone h.1)
  have opIn := hSame.inBounds
  have hBranchCtx : op.IsLlvmBranch ctx.raw := by
    simpa [OperationPtr.IsLlvmBranch, hSame.opType] using hBranch
  have hNumOperands : op.getNumOperands! ctx.raw = op.getNumOperands! ctx₀.raw := by
    rw [← OperationPtr.getOperands!.size_eq_getNumOperands!, hSame.operands]
    simp [OperationPtr.getOperands!.size_eq_getNumOperands!]
  have hOperand : ∀ i, op.getOperand! ctx.raw i = op.getOperand! ctx₀.raw i := by
    intro i
    rw [← OperationPtr.getOperands!.getElem!_eq_getOperand!, hSame.operands]
    simp [OperationPtr.getOperands!.getElem!_eq_getOperand!]
  /- An operation of `ctx` that is not the branch stays the same. -/
  have hOther : ∀ o', o'.InBounds ctx.raw → ¬ o'.IsLlvmBranch ctx.raw →
      OpSame id ctx.raw ctx'.raw o' :=
    fun o' oIn' hB => hStep.ops o' oIn' (fun hEq => hB (hEq ▸ hBranchCtx))
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
      have hSize : casts.size = o.getNumOperands! ctx₀.raw := hStep.size.trans hNumOperands
      have hGet : ∀ i (hi : i < o.getNumOperands! ctx₀.raw), casts[i]! = casts[i]'(hSize ▸ hi) :=
        fun i hi => getElem!_pos casts i (hSize ▸ hi)
      refine ⟨hResults, fun i hi => ?_, fun i j hi hj hEq => ?_, hStep.newIn,
        hStep.newResultTypes, hStep.newSuccessors.trans hSame.successors, ?_,
        fun hB => hStep.newBr (hSame.opType.trans hB), fun hB => ?_⟩
      · rw [hGet i hi]
        obtain ⟨c₁, c₂, c₃, c₄, c₅, c₆⟩ := hStep.cast i (hSize ▸ hi)
        refine ⟨c₁, fun r rIn hr => ?_, c₃, c₄, by rw [c₅, hOperand], ?_⟩
        · obtain ⟨rOpIn, hIndex⟩ := OpResultPtr.inBounds_def.mp rIn
          have hNotLowered : ¬ (r.op ∈ done ∧ r.op.IsLlvmBranch ctx₀.raw) := fun h => by
            have := (hInv.branch r.op h.1 h.2).numResults
            grind
          exact c₂ (hr ▸ (hInv.ops r.op rOpIn hNotLowered).inBounds)
        · rw [hOperand] at c₆
          rwa [← (hInv.types _ (OperationPtr.getOperands!_inBounds ctx₀.wellFormed.inBounds opIn₀
            (OperationPtr.getOperands!.mem_getOperand hi))).2]
      · rw [hGet i hi, hGet j hj] at hEq
        exact hStep.nodup.eq_of_getElem_eq (by simpa [hSize] using hi) (by simpa [hSize] using hj)
          (by simpa using hEq)
      · rw [hStep.newOperands]
        apply Array.ext
        · simp [hSize]
        · intro i h₁ h₂
          simp only [Array.getElem_map, Array.getElem_range]
          rw [getElem!_pos casts i (by simpa using h₁)]
      · have hNe : o.getOpType! ctx.raw ≠ .llvm .br := by rw [hSame.opType, hB]; simp
        exact ⟨(hStep.newCondBr hNe).1, by rw [(hStep.newCondBr hNe).2, hSame.properties]⟩
    · have hMem' : o ∈ done := by simpa [hEq] using hMem
      simp only [hEq, ↓reduceIte]
      exact (hInv.branch o hMem' hB).mono hB hOther
  · rw [hStep.opList block (hInv.ctxSame.blockIn blockIn), hInv.opList block blockIn]
    simp only [List.replaceBy, List.flatMap_assoc]
    congr 1
    funext o
    by_cases hEq : o = op
    · subst hEq
      have hSize : casts.size = o.getNumOperands! ctx₀.raw := hStep.size.trans hNumOperands
      simp only [hNotDone, false_and, ↓reduceIte, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.mem_cons, true_or, hBranch, and_self]
      rw [Array.toList_eq_map_range, hSize]
    · by_cases hLowered : o ∈ done ∧ o.IsLlvmBranch ctx₀.raw
      · have hFacts := hInv.branch o hLowered.1 hLowered.2
        have hMem : o ∈ op :: done := List.mem_cons_of_mem _ hLowered.1
        simp only [hLowered, and_self, ↓reduceIte, hMem, hEq]
        /- Neither a cast nor a RISC-V branch is the LLVM branch that is lowered now. -/
        have hNotMem : op ∉ (List.range (o.getNumOperands! ctx₀.raw)).map (operandCast o) ++
            [newBranch o] := by
          intro hOp
          rcases List.mem_append.mp hOp with hOp | hOp
          · obtain ⟨i, hi, hCast⟩ := List.mem_map.mp hOp
            have := (hFacts.cast i (by simpa using hi)).2.2.1
            rw [hCast] at this
            rcases hBranchCtx with h | h <;> simp [h] at this
          · obtain rfl : op = newBranch o := by simpa using hOp
            rcases hLowered.2 with hB | hB
            · have := hFacts.newBr hB
              rcases hBranchCtx with h | h <;> simp [h] at this
            · have := (hFacts.newCondBr hB).1
              rcases hBranchCtx with h | h <;> simp [h] at this
        exact List.replaceBy_of_not_mem hNotMem
      · simp [hLowered, hEq]

theorem PhaseA.step {ctx₀ ctx ctx' : WfIRContext OpCode} {done : List OperationPtr}
    {operandCast newBranch} {op : OperationPtr}
    (hInv : PhaseA ctx₀ ctx done operandCast newBranch)
    (opIn₀ : op.InBounds ctx₀.raw) (hNotDone : op ∉ done)
    (hNotUnreachable : op.getOpType! ctx₀.raw ≠ OpCode.llvm .unreachable)
    (h : convertBranch ctx op = .ok ctx') :
    ∃ operandCast' newBranch', PhaseA ctx₀ ctx' (op :: done) operandCast' newBranch' := by
  have hSame := hInv.ops op opIn₀ (fun h => hNotDone h.1)
  have hBranchIff : op.IsLlvmBranch ctx.raw ↔ op.IsLlvmBranch ctx₀.raw := by
    simp [OperationPtr.IsLlvmBranch, hSame.opType]
  rcases convertBranch_ok (by rw [hSame.opType]; exact hNotUnreachable) h with
    ⟨hBranch, hSuccessors, rfl⟩ | ⟨hBranch, hResults, hLower⟩
  · refine ⟨operandCast, newBranch, hInv.step_other (by rwa [← hBranchIff]) ?_⟩
    rw [← OperationPtr.getSuccessors!.size_eq_getNumSuccessors!, ← hSame.successors,
      OperationPtr.getSuccessors!.size_eq_getNumSuccessors!, hSuccessors]
  · obtain ⟨casts, newOp, hStep⟩ := lowerBranch_spec hSame.inBounds hLower
    refine ⟨_, _, hInv.step_branch opIn₀ hNotDone (hBranchIff.mp hBranch) ?_ hStep⟩
    rw [← OperationPtr.getResultTypes!.size_eq_getNumResults!, ← hSame.resultTypes,
      OperationPtr.getResultTypes!.size_eq_getNumResults!, hResults]

theorem PhaseA.foldlM {ctx₀ ctx ctx' : WfIRContext OpCode} {done rest : List OperationPtr}
    {operandCast newBranch}
    (hInv : PhaseA ctx₀ ctx done operandCast newBranch)
    (restIn : ∀ o ∈ rest, o.InBounds ctx₀.raw) (hNodup : rest.Nodup)
    (hDisjoint : ∀ o ∈ rest, o ∉ done)
    (hNotUnreachable : ∀ o ∈ rest, o.getOpType! ctx₀.raw ≠ OpCode.llvm .unreachable)
    (h : rest.foldlM convertBranch ctx = .ok ctx') :
    ∃ done' operandCast' newBranch', PhaseA ctx₀ ctx' done' operandCast' newBranch' ∧
      ∀ o, o ∈ done' ↔ o ∈ rest ∨ o ∈ done := by
  induction rest generalizing ctx done operandCast newBranch with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨done, operandCast, newBranch, hInv, by simp⟩
  | cons op rest ih =>
    simp only [List.foldlM_cons, bind, Except.bind] at h
    split at h
    next => simp at h
    next ctx₁ hStep =>
      obtain ⟨operandCast₁, newBranch₁, hInv₁⟩ :=
        hInv.step (restIn op (by simp)) (hDisjoint op (by simp))
          (hNotUnreachable op (by simp)) hStep
      have hNodup' := List.nodup_cons.mp hNodup
      obtain ⟨done', operandCast', newBranch', hInv', hMem⟩ := ih hInv₁
        (fun o ho => restIn o (by simp [ho])) hNodup'.2
        (fun o ho hMem => by
          rcases List.mem_cons.mp hMem with rfl | hMem
          · exact hNodup'.1 ho
          · exact hDisjoint o (by simp [ho]) hMem)
        (fun o ho => hNotUnreachable o (by simp [ho])) h
      exact ⟨done', operandCast', newBranch', hInv', fun o => by rw [hMem o]; simp only [List.mem_cons]; grind⟩

/-! ## Converting the arguments of a block -/

theorem convertBlockArgument_ok {block : BlockPtr} {ctx ctx' : WfIRContext OpCode} {i : Nat}
    (h : convertBlockArgument block ctx i = .ok ctx') :
    let arg : BlockArgumentPtr := ⟨block, i⟩
    let ctx₁ := WfRewriter.setType! ctx (.blockArgument arg) (RegisterType.mk : TypeAttr)
    fitsRegister ((ValuePtr.blockArgument arg).getType! ctx.raw) ∧
    ∃ ctx₂ cast,
      WfRewriter.createOp! ctx₁ (OpCode.builtin .unrealized_conversion_cast)
        #[(ValuePtr.blockArgument arg).getType! ctx.raw] #[] #[] #[] default
        (some (InsertPoint.atStart! block ctx₁.raw)) = some (ctx₂, cast) ∧
      ctx' = WfRewriter.pushOperand!
        (WfRewriter.replaceValue! ctx₂ (.blockArgument arg) (cast.getResult 0)) cast
        (.blockArgument arg) := by
  simp only [convertBlockArgument] at h
  split at h
  next => simp [throw, throwThe, MonadExceptOf.throw] at h
  next hFits =>
    split at h
    next ctx₂ cast hCreate =>
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact ⟨by simpa using hFits, ctx₂, cast, hCreate, h.symm⟩
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
  fits : fitsRegister ((ValuePtr.blockArgument arg).getType! ctx.raw)
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
  obtain ⟨hFits, ctx₂, cast, hCreate, rfl⟩ := convertBlockArgument_ok h
  have hArg : (⟨arg.block, arg.index⟩ : BlockArgumentPtr) = arg := rfl
  simp only [hArg] at hFits hCreate ⊢
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
    fits := hFits
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
    fitsRegister ((ValuePtr.blockArgument arg).getType! ctx₀.raw) ∧
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
      exact ⟨argIn₀, this ▸ hStep.fits, hStep.castIn,
        fun h => hStep.castNotIn (hInv.ops _ h).inBounds, hStep.castType,
        this ▸ hStep.castResultTypes, hStep.castOperands⟩
    · obtain ⟨c₁, c₂, c₃, c₄, c₅, c₆, c₇⟩ := hInv.args a ha
      have hS := hStep.ops (argCast a) c₃
      simp only [hOld a ha, ↓reduceIte]
      refine ⟨c₁, c₂, hS.inBounds, c₄, hS.opType.trans c₅, hS.resultTypes.trans c₆, ?_⟩
      rw [hS.operands, c₇]
      simp [substArg, hOld a ha]
  · by_cases e₁ : a₁ = arg <;> by_cases e₂ : a₂ = arg
    · rw [e₁, e₂]
    · have m₂ : a₂ ∈ done := by simpa [e₂] using h₂
      simp only [e₁, e₂, ↓reduceIte] at hEq
      exact absurd (hEq ▸ (hInv.args a₂ m₂).2.2.1) hStep.castNotIn
    · have m₁ : a₁ ∈ done := by simpa [e₁] using h₁
      simp only [e₁, e₂, ↓reduceIte] at hEq
      exact absurd (hEq ▸ (hInv.args a₁ m₁).2.2.1) hStep.castNotIn
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
def blockArgsReversed (ctx : IRContext OpCode) (block : BlockPtr) : List BlockArgumentPtr :=
  (List.range (block.getNumArguments! ctx)).reverse.map (⟨block, ·⟩)

/-- The module after the blocks `blocks` were converted. -/
structure PhaseBlocks (ctx₀ ctx : WfIRContext OpCode) (blocks : List BlockPtr)
    (done : List BlockArgumentPtr) (argCast : BlockArgumentPtr → OperationPtr) : Prop where
  phase : PhaseB ctx₀ ctx done argCast
  blocksIn : ∀ block ∈ blocks, block.InBounds ctx₀.raw
  argsOf : ∀ block : BlockPtr, done.filter (·.block = block) =
    if block ∈ blocks then blockArgsReversed ctx₀.raw block else []

theorem PhaseBlocks.step {ctx₀ ctx ctx' : WfIRContext OpCode} {blocks : List BlockPtr}
    {done : List BlockArgumentPtr} {argCast} {block : BlockPtr}
    (hInv : PhaseBlocks ctx₀ ctx blocks done argCast) (blockIn₀ : block.InBounds ctx₀.raw)
    (hNotDone : block ∉ blocks) (h : convertBlock ctx block = .ok ctx') :
    ∃ done' argCast', PhaseBlocks ctx₀ ctx' (block :: blocks) done' argCast' := by
  have hFold : (List.range (block.getNumArguments! ctx.raw)).foldlM
      (convertBlockArgument block) ctx = .ok ctx' := h
  have hNum := hInv.phase.ctxSame.numArguments blockIn₀
  rw [hNum] at hFold
  have hNone : ∀ arg ∈ done, arg.block ≠ block := fun arg hArg hEq => by
    have := hInv.argsOf block
    simp only [hNotDone, ↓reduceIte] at this
    have hMem : arg ∈ done.filter (·.block = block) := List.mem_filter.mpr ⟨hArg, by simp [hEq]⟩
    simp [this] at hMem
  obtain ⟨argCast', hPhase⟩ := hInv.phase.foldArgs (block := block)
    (indices := List.range (block.getNumArguments! ctx₀.raw))
    (fun i hi => BlockArgumentPtr.inBounds_def.mpr ⟨blockIn₀, by
      have : i < block.getNumArguments! ctx₀.raw := by simpa using hi
      grind⟩)
    List.nodup_range (fun i _ hMem => hNone _ hMem rfl) hFold
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
      simp [blockArgsReversed]
    · have hFirst : ((List.range (block.getNumArguments! ctx₀.raw)).reverse.map
          (fun i => (⟨block, i⟩ : BlockArgumentPtr))).filter (·.block = b) = [] := by
        rw [List.filter_eq_nil_iff]
        intro a ha
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
        simpa using fun h => hEq h.symm
      rw [hFirst, List.nil_append, hInv.argsOf b]
      simp [hEq]

theorem PhaseBlocks.foldlM {ctx₀ ctx ctx' : WfIRContext OpCode} {blocks blocks' targets : List BlockPtr}
    {done : List BlockArgumentPtr} {argCast}
    (hInv : PhaseBlocks ctx₀ ctx blocks done argCast)
    (targetsIn : ∀ block ∈ targets, block.InBounds ctx₀.raw)
    (h : targets.foldlM convertBlockOnce (ctx, blocks) = .ok (ctx', blocks')) :
    ∃ done' argCast', PhaseBlocks ctx₀ ctx' blocks' done' argCast' ∧
      ∀ block, block ∈ blocks' ↔ block ∈ targets ∨ block ∈ blocks := by
  induction targets generalizing ctx blocks done argCast with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨done, argCast, hInv, by simp⟩
  | cons block targets ih =>
    simp only [List.foldlM_cons, bind, Except.bind] at h
    split at h
    next => simp at h
    next acc hStep =>
      obtain ⟨ctx₁, blocks₁⟩ := acc
      simp only [convertBlockOnce] at hStep
      split at hStep
      next hMem =>
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hStep
        obtain ⟨rfl, rfl⟩ := hStep
        obtain ⟨done', argCast', hInv', hIff⟩ := ih hInv
          (fun b hb => targetsIn b (by simp [hb])) h
        exact ⟨done', argCast', hInv', fun b => by rw [hIff b]; simp only [List.mem_cons]; grind⟩
      next hNotMem =>
        simp only [bind, Except.bind] at hStep
        split at hStep
        next => simp at hStep
        next ctx₂ hConvert =>
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hStep
          obtain ⟨rfl, rfl⟩ := hStep
          obtain ⟨done₁, argCast₁, hInv₁⟩ := hInv.step (targetsIn block (by simp)) hNotMem hConvert
          obtain ⟨done', argCast', hInv', hIff⟩ := ih hInv₁
            (fun b hb => targetsIn b (by simp [hb])) h
          exact ⟨done', argCast', hInv', fun b => by
            rw [hIff b]; simp only [List.mem_cons]; grind⟩

/-! ## The two phases give a branch lowering -/

section assemble

variable {ctx₀ ctxA ctx' : WfIRContext OpCode} {doneOps : List OperationPtr}
  {operandCast : OperationPtr → Nat → OperationPtr} {newBranch : OperationPtr → OperationPtr}
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
    simp only [hIn, iff_true, blockArgsReversed, List.mem_map, List.mem_reverse, List.mem_range]
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

/-- The module after both phases is the branch lowering of the module before them. -/
def BranchLowering.ofPhases (hA : PhaseA ctx₀ ctxA doneOps operandCast newBranch)
    (hDone : ∀ o : OperationPtr, o.InBounds ctx₀.raw → o ∈ doneOps)
    (hB : PhaseBlocks ctxA ctx' blocks doneArgs argCast)
    (hTargets : ∀ (op : OperationPtr) (block : BlockPtr), op.InBounds ctx₀.raw →
      op.IsLlvmBranch ctx₀.raw → block ∈ op.getSuccessors! ctx₀.raw → block ∈ blocks)
    (hBranchedTo : ∀ block ∈ blocks, ∃ op : OperationPtr, op.InBounds ctx₀.raw ∧
      block ∈ op.getSuccessors! ctx₀.raw)
    {root : OperationPtr} (hVerified : ctx₀.Verified root) :
    BranchLowering ctx₀ ctx' where
  converted := fun block => decide (block ∈ blocks)
  argCast := argCast
  operandCast := operandCast
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
      · simp [hMem, blockArgsReversed, hA.ctxSame.numArguments hBlock, BlockPtr.getArgument_def]
      · simp [hMem]
    · apply List.flatMap_congr_of_mem
      intro o ho
      have oIn : o.InBounds ctx₀.raw := by
        have := BlockPtr.operationListWF ctx₀.raw block hBlock ctx₀.wellFormed
        exact this.arrayInBounds (by simpa using ho)
      simp [lowerOp, hDone o oIn]
  regionIn := fun h => hB.phase.ctxSame.regionIn (hA.ctxSame.regionIn h)
  firstBlock := fun h =>
    (hB.phase.ctxSame.firstBlock (hA.ctxSame.regionIn h)).trans (hA.ctxSame.firstBlock h)
  entryNotConverted := fun {region block} regionIn hFirst => by
    apply Classical.byContradiction
    intro hConverted
    /- A converted block is branched to, which the verifier forbids for an entry block. -/
    obtain ⟨op, opIn, hSuccessor⟩ := hBranchedTo block (by simpa using hConverted)
    exact BlockPtr.firstUse_ne_none_of_successor opIn hSuccessor
      (hVerified.entryBlock_firstUse_eq_none
        (OperationPtr.getSuccessors!_inBounds opIn hSuccessor)
        (RegionPtr.parent_of_firstBlock regionIn hFirst) hFirst)
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
    exact ⟨hTypeB, hTypeA.2 ▸ (hB.phase.args _ hDoneArg).2.1⟩
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
    obtain ⟨_, _, c₃, c₄, c₅, c₆, c₇⟩ := hB.phase.args arg hDoneArg
    refine ⟨c₃, fun result resultIn hEq => ?_, c₅, hTypeA.2 ▸ c₆, c₇⟩
    obtain ⟨opIn, hIndex⟩ := OpResultPtr.inBounds_def.mp resultIn
    have hNotLowered : ¬ (result.op ∈ doneOps ∧ result.op.IsLlvmBranch ctx₀.raw) := fun h => by
      have := (hA.branch result.op h.1 h.2).numResults
      grind
    exact c₄ (hEq ▸ (hA.ops result.op opIn hNotLowered).inBounds)
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
  operandCastSpec := fun {op i} opIn hBranch hi => by
    have hFacts := hA.branch op (hDone op opIn) hBranch
    obtain ⟨c₁, c₂, c₃, c₄, c₅, c₆⟩ := hFacts.cast i hi
    have sB := hB.phase.ops (operandCast op i) c₁
    have operandIn := OperationPtr.getOperands!_inBounds ctx₀.wellFormed.inBounds opIn
      (OperationPtr.getOperands!.mem_getOperand hi)
    refine ⟨sB.inBounds, c₂, sB.opType.trans c₃, sB.resultTypes.trans c₄, ?_, c₆,
      fun arg argIn hConverted hEq => ?_⟩
    · rw [sB.operands, c₅]
      simpa using hB.lowerArgs_eq (hA.types _ operandIn).1
    · have hDoneArg : arg ∈ doneArgs := (hB.mem_done_iff (by
        simpa using (hA.types (.blockArgument arg) (by simpa using argIn)).1)).mpr
        (by simpa using hConverted)
      exact (hB.phase.args arg hDoneArg).2.2.2.1 (hEq ▸ c₁)
  operandCastInj := fun opIn hBranch hi hj hEq =>
    (hA.branch _ (hDone _ opIn) hBranch).castInj _ _ hi hj hEq
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
    exact (hB.phase.ops (newBranch op) hFacts.newIn).opType.trans (hFacts.newBr hType)
  newBranchCondBr := fun {op} opIn hType => by
    have hFacts := hA.branch op (hDone op opIn) (.inr hType)
    have sB := hB.phase.ops (newBranch op) hFacts.newIn
    exact ⟨sB.opType.trans (hFacts.newCondBr hType).1,
      by rw [sB.properties]; exact (hFacts.newCondBr hType).2⟩

end assemble

/-! ## The pass -/

/-- A module that `convertModule` returns is the branch lowering of its input. -/
theorem convertModule_branchLowering {ctx ctx' : WfIRContext OpCode} {root : OperationPtr}
    (hVerified : ctx.Verified root)
    (hNoUnreachable : ∀ o : OperationPtr, o.InBounds ctx.raw →
      o.getOpType! ctx.raw ≠ OpCode.llvm .unreachable)
    (h : convertModule ctx = .ok ctx') :
    Nonempty (BranchLowering ctx ctx') := by
  simp only [convertModule, bind, Except.bind] at h
  split at h
  next => simp at h
  next ctxA hLower =>
    split at h
    next => simp at h
    next acc hConvert =>
      obtain ⟨ctxB, blocks⟩ := acc
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      have hKeys : ∀ o : OperationPtr, o ∈ ctx.raw.operations.keys ↔ o.InBounds ctx.raw := fun o => by
        rw [Std.HashMap.mem_keys, OperationPtr.inBounds_def]
      have hNodup : ctx.raw.operations.keys.Nodup := by
        have := ctx.raw.operations.distinct_keys
        simpa [List.Nodup] using this
      obtain ⟨doneOps, operandCast, newBranch, hA, hDoneOps⟩ :=
        (PhaseA.init (operandCast := fun _ _ => default) (newBranch := fun _ => default)).foldlM
          (fun o ho => (hKeys o).mp ho) hNodup (fun _ _ h => by simp at h)
          (fun o ho => hNoUnreachable o ((hKeys o).mp ho)) hLower
      have hTargetsIn : ∀ block ∈ branchTargets ctx.raw ctx.raw.operations.keys,
          block.InBounds ctxA.raw := by
        intro block hBlock
        obtain ⟨op, hOp, hMem⟩ := List.mem_flatMap.mp hBlock
        split at hMem
        · have opIn := (hKeys op).mp hOp
          have hSucc : block ∈ op.getSuccessors! ctx.raw := by simpa using hMem
          exact hA.ctxSame.blockIn (OperationPtr.getSuccessors!_inBounds opIn hSucc)
        · simp at hMem
      obtain ⟨doneArgs, argCast, hB, hBlocks⟩ :=
        (PhaseBlocks.foldlM (argCast := fun _ => default)
          ⟨PhaseB.init, fun _ h => by simp at h, fun _ => by simp⟩
          hTargetsIn hConvert)
      refine ⟨BranchLowering.ofPhases hA (fun o oIn => (hDoneOps o).mpr (.inl ((hKeys o).mpr oIn)))
        hB (fun op block opIn hBranch hMem => (hBlocks block).mpr (.inl ?_))
        (fun block hBlock => ?_) hVerified⟩
      · exact List.mem_flatMap.mpr ⟨op, (hKeys op).mpr opIn, by simp [hBranch, hMem]⟩
      · rcases (hBlocks block).mp hBlock with hTarget | hNil
        · obtain ⟨op, hOp, hMem⟩ := List.mem_flatMap.mp hTarget
          split at hMem
          · exact ⟨op, (hKeys op).mp hOp, by simpa using hMem⟩
          · simp at hMem
        · simp at hNil

/--
  The RISC-V branch lowering refines a module that verifies and holds no
  `llvm.unreachable`: every function of the input is refined by the function of
  the same name in the module the pass returns.

  The lowering also replaces an `llvm.unreachable` by `riscv_cf.unreachable`,
  which this proof does not cover: an operation that is neither left alone nor
  lowered as a branch is a shape `PhaseA` does not describe.
-/
theorem convertModule_isModuleRefinedBy {ctx ctx' : WfIRContext OpCode} {root : OperationPtr}
    (hVerified : ctx.Verified root)
    (hNoUnreachable : ∀ o : OperationPtr, o.InBounds ctx.raw →
      o.getOpType! ctx.raw ≠ OpCode.llvm .unreachable)
    (h : convertModule ctx = .ok ctx') (module : OperationPtr) :
    module.isModuleRefinedBy ctx module ctx' true :=
  (convertModule_branchLowering hVerified hNoUnreachable h).elim fun lowering =>
    lowering.isModuleRefinedBy module

end Veir
