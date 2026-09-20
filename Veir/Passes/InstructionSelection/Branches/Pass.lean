module

public import Veir.Passes.InstructionSelection.Branches.Frame
public import Veir.Passes.InstructionSelection.Branches.Simulation

import all Veir.Passes.InstructionSelection.RISCV64Branches

public section

/-!
# The pass computes a branch lowering

`convertModule` succeeds only with a module that is the `BranchLowering` of its
input, so the module it returns refines the one it was given.
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

theorem convertBranch_ok {ctx ctx' : WfIRContext OpCode} {op : OperationPtr}
    (h : convertBranch ctx op = .ok ctx') :
    (¬ op.IsLlvmBranch ctx.raw ∧ op.getNumSuccessors! ctx.raw = 0 ∧ ctx' = ctx) ∨
    (op.IsLlvmBranch ctx.raw ∧ op.getNumResults! ctx.raw = 0 ∧ lowerBranch ctx op = .ok ctx') := by
  simp only [convertBranch] at h
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
    (h : convertBranch ctx op = .ok ctx') :
    ∃ operandCast' newBranch', PhaseA ctx₀ ctx' (op :: done) operandCast' newBranch' := by
  have hSame := hInv.ops op opIn₀ (fun h => hNotDone h.1)
  have hBranchIff : op.IsLlvmBranch ctx.raw ↔ op.IsLlvmBranch ctx₀.raw := by
    simp [OperationPtr.IsLlvmBranch, hSame.opType]
  rcases convertBranch_ok h with ⟨hBranch, hSuccessors, rfl⟩ | ⟨hBranch, hResults, hLower⟩
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
        hInv.step (restIn op (by simp)) (hDisjoint op (by simp)) hStep
      have hNodup' := List.nodup_cons.mp hNodup
      obtain ⟨done', operandCast', newBranch', hInv', hMem⟩ := ih hInv₁
        (fun o ho => restIn o (by simp [ho])) hNodup'.2
        (fun o ho hMem => by
          rcases List.mem_cons.mp hMem with rfl | hMem
          · exact hNodup'.1 ho
          · exact hDisjoint o (by simp [ho]) hMem) h
      exact ⟨done', operandCast', newBranch', hInv', fun o => by rw [hMem o]; simp only [List.mem_cons]; grind⟩

end Veir
