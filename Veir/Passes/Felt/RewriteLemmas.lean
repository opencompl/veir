import Veir.Passes.Matching
import Veir.Passes.Felt.Matching
import Veir.Passes.Felt.InterpModel

namespace Veir

theorem matchOp_spec {op : OperationPtr} {ctx : IRContext OpCode} {opType : OpCode}
    {n : Nat} {r : Array ValuePtr × propertiesOf opType}
    (h : matchOp op ctx opType n = some r) :
    op.getOpType! ctx = opType ∧ op.getNumOperands! ctx = n ∧ op.getNumResults! ctx = 1 := by
  simp only [matchOp, bind, Option.bind, guard, pure, failure] at h
  grind

/-- Generalized in-bounds: a successful `matchOp` for ANY `opType` (whose value differs
    from the default operation's opType) implies the matched op is in bounds. The
    per-opcode wrappers below pin `opType` so `decide` discharges the inequality. -/
theorem matchOp_inBounds {op : OperationPtr} {ctx : IRContext OpCode} {opType : OpCode}
    {n : Nat} {r : Array ValuePtr × propertiesOf opType}
    (hd : (default : Operation OpCode).opType ≠ opType)
    (h : matchOp op ctx opType n = some r) : op.InBounds ctx := by
  have hspec := (matchOp_spec h).1
  refine Decidable.byContradiction (fun hb => ?_)
  rw [OperationPtr.getOpType!, OperationPtr.get!_of_not_inBounds hb] at hspec
  exact absurd hspec hd

theorem matchOp_inBounds_add {op : OperationPtr} {ctx : IRContext OpCode} {n : Nat}
    {r : Array ValuePtr × propertiesOf (OpCode.felt Felt.add)}
    (h : matchOp op ctx (OpCode.felt Felt.add) n = some r) : op.InBounds ctx :=
  matchOp_inBounds (by decide) h

theorem matchOp_inBounds_mul {op : OperationPtr} {ctx : IRContext OpCode} {n : Nat}
    {r : Array ValuePtr × propertiesOf (OpCode.felt Felt.mul)}
    (h : matchOp op ctx (OpCode.felt Felt.mul) n = some r) : op.InBounds ctx :=
  matchOp_inBounds (by decide) h

theorem matchOp_inBounds_sub {op : OperationPtr} {ctx : IRContext OpCode} {n : Nat}
    {r : Array ValuePtr × propertiesOf (OpCode.felt Felt.sub)}
    (h : matchOp op ctx (OpCode.felt Felt.sub) n = some r) : op.InBounds ctx :=
  matchOp_inBounds (by decide) h

theorem matchOp_inBounds_neg {op : OperationPtr} {ctx : IRContext OpCode} {n : Nat}
    {r : Array ValuePtr × propertiesOf (OpCode.felt Felt.neg)}
    (h : matchOp op ctx (OpCode.felt Felt.neg) n = some r) : op.InBounds ctx :=
  matchOp_inBounds (by decide) h

theorem matchOp_inBounds_const {op : OperationPtr} {ctx : IRContext OpCode} {n : Nat}
    {r : Array ValuePtr × propertiesOf (OpCode.felt Felt.const)}
    (h : matchOp op ctx (OpCode.felt Felt.const) n = some r) : op.InBounds ctx :=
  matchOp_inBounds (by decide) h

/-- The operands array returned by a successful `matchOp` equals the op's operands. -/
theorem matchOp_operands_eq {op : OperationPtr} {ctx : IRContext OpCode} {opType : OpCode}
    {n : Nat} {o : Array ValuePtr} {p : propertiesOf opType}
    (hb : matchOp op ctx opType n = some (o, p)) : o = op.getOperands! ctx := by
  simp only [matchOp, bind, Option.bind, guard, pure] at hb; grind

/-- A matched op with a single result has its 0-th result in bounds. -/
theorem getResult0_inBounds {op : OperationPtr} {ctx : IRContext OpCode}
    (hIn : op.InBounds ctx) (hNumRes : op.getNumResults! ctx = 1) :
    (op.getResult 0 : ValuePtr).InBounds ctx := by
  rw [ValuePtr.inBounds_opResult]
  exact op.getResult_inBounds hIn 0 (by grind)

/-- Operand `i` (for `i < numOperands`) of an in-bounds op is in bounds. -/
theorem getOperand_inBounds {op : OperationPtr} {ctx : IRContext OpCode}
    (hFib : ctx.FieldsInBounds) (hIn : op.InBounds ctx) (i : Nat)
    (hi : i < op.getNumOperands! ctx) : (op.getOperands! ctx)[i]!.InBounds ctx := by
  have hsize : (op.getOperands! ctx).size = op.getNumOperands! ctx :=
    OperationPtr.getOperands!.size_eq_getNumOperands!
  have hmem : (op.getOperands! ctx)[i]! ∈ op.getOperands! ctx := by
    rw [OperationPtr.getOperands!.getElem!_eq_getOperand!,
      ← OperationPtr.getOperands!.getElem_eq_getOperand! (h := by omega)]
    exact Array.getElem_mem (by omega)
  exact OperationPtr.getOperands!_inBounds hFib hIn hmem

namespace FeltPass

/-- Build a folded felt constant through LLZK's accepted field registry.
    Bare or unknown fields do not fold because their modulus is intentionally
    unresolved. -/
def foldedConstProperties? (fieldType : FeltType) (raw : Int) :
    Option FeltConstProperties :=
  match FeltInterp.feltPrime fieldType.fieldName with
  | none => none
  | some p =>
    let value := Int.ofNat (FeltInterp.reduce p raw)
    some { value := { value, fieldType } }

theorem matchAdd_inBounds {op : OperationPtr} {ctx : IRContext OpCode}
    {r : ValuePtr × ValuePtr × propertiesOf (OpCode.felt Felt.add)}
    (h : matchAdd op ctx = some r) : op.InBounds ctx := by
  unfold matchAdd at h
  simp only [bind, Option.bind] at h
  split at h <;> first | exact matchOp_inBounds_add (by assumption) | simp_all

theorem matchMul_inBounds {op : OperationPtr} {ctx : IRContext OpCode}
    {r : ValuePtr × ValuePtr × propertiesOf (OpCode.felt Felt.mul)}
    (h : matchMul op ctx = some r) : op.InBounds ctx := by
  unfold matchMul at h
  simp only [bind, Option.bind] at h
  split at h <;> first | exact matchOp_inBounds_mul (by assumption) | simp_all

theorem matchSub_inBounds {op : OperationPtr} {ctx : IRContext OpCode}
    {r : ValuePtr × ValuePtr × propertiesOf (OpCode.felt Felt.sub)}
    (h : matchSub op ctx = some r) : op.InBounds ctx := by
  unfold matchSub at h
  simp only [bind, Option.bind] at h
  split at h <;> first | exact matchOp_inBounds_sub (by assumption) | simp_all

theorem matchNeg_inBounds {op : OperationPtr} {ctx : IRContext OpCode}
    {r : ValuePtr × propertiesOf (OpCode.felt Felt.neg)}
    (h : matchNeg op ctx = some r) : op.InBounds ctx := by
  unfold matchNeg at h
  simp only [bind, Option.bind] at h
  split at h <;> first | exact matchOp_inBounds_neg (by assumption) | simp_all

theorem matchConst_inBounds {op : OperationPtr} {ctx : IRContext OpCode}
    {r : propertiesOf (OpCode.felt Felt.const)}
    (h : matchConst op ctx = some r) : op.InBounds ctx := by
  unfold matchConst at h
  simp only [bind, Option.bind] at h
  split at h <;> first | exact matchOp_inBounds_const (by assumption) | simp_all

/-- `replaceValue` preserves an operation's region count. -/
theorem getNumRegions!_replaceValue
    (rewriter : PatternRewriter OpCode) (oldVal newVal : ValuePtr) (op : OperationPtr)
    (hNe : oldVal ≠ newVal)
    (oldIn : oldVal.InBounds rewriter.ctx.raw) (newIn : newVal.InBounds rewriter.ctx.raw)
    : op.getNumRegions! (rewriter.replaceValue oldVal newVal hNe oldIn newIn).ctx.raw =
      op.getNumRegions! rewriter.ctx.raw := by
  unfold PatternRewriter.replaceValue
  simp [PatternRewriter.addUsersInWorklist_same_ctx]

/-- `replaceValue` preserves `InBounds` of an operation. -/
theorem inBounds_replaceValue
    (rewriter : PatternRewriter OpCode) (oldVal newVal : ValuePtr) (op : OperationPtr)
    (hNe : oldVal ≠ newVal)
    (oldIn : oldVal.InBounds rewriter.ctx.raw) (newIn : newVal.InBounds rewriter.ctx.raw)
    (hOp : op.InBounds rewriter.ctx.raw) :
    op.InBounds (rewriter.replaceValue oldVal newVal hNe oldIn newIn).ctx.raw := by
  unfold PatternRewriter.replaceValue
  simp only [PatternRewriter.addUsersInWorklist_same_ctx]
  have hGeneric :
      (GenericPtr.operation op).InBounds
        (WfRewriter.replaceValue rewriter.ctx oldVal newVal hNe oldIn newIn).raw := by
    rw [WfRewriter.replaceValue_inBounds]
    exact hOp
  exact hGeneric

/-- `replaceValue` preserves an operation's result count. -/
theorem getNumResults!_replaceValue
    (rewriter : PatternRewriter OpCode) (oldVal newVal : ValuePtr) (op : OperationPtr)
    (hNe : oldVal ≠ newVal)
    (oldIn : oldVal.InBounds rewriter.ctx.raw) (newIn : newVal.InBounds rewriter.ctx.raw)
    : op.getNumResults! (rewriter.replaceValue oldVal newVal hNe oldIn newIn).ctx.raw =
      op.getNumResults! rewriter.ctx.raw := by
  unfold PatternRewriter.replaceValue
  simp [PatternRewriter.addUsersInWorklist_same_ctx]

/-- Replacing all uses of `oldVal` by a distinct `newVal` leaves `oldVal` use-free. -/
theorem hasUses!_oldVal_WfRewriter_replaceValue
    (ctx : WfIRContext OpCode) (oldVal newVal : ValuePtr)
    (hNe : oldVal ≠ newVal)
    (oldIn : oldVal.InBounds ctx.raw) (newIn : newVal.InBounds ctx.raw) :
    oldVal.hasUses! (WfRewriter.replaceValue ctx oldVal newVal hNe oldIn newIn).raw = false := by
  fun_induction WfRewriter.replaceValue <;>
    grind [Id.run, pure, ValuePtr.hasUses!_def, ValuePtr.getFirstUse!_eq_getFirstUse]

/-- After `replaceValue oldVal newVal` (with `oldVal ≠ newVal`), `oldVal` has no uses. -/
theorem hasUses!_oldVal_replaceValue
    (rewriter : PatternRewriter OpCode) (oldVal newVal : ValuePtr)
    (oldIn : oldVal.InBounds rewriter.ctx.raw) (newIn : newVal.InBounds rewriter.ctx.raw)
    (hNe : oldVal ≠ newVal) :
    oldVal.hasUses! (rewriter.replaceValue oldVal newVal hNe oldIn newIn).ctx.raw = false := by
  unfold PatternRewriter.replaceValue
  simp [PatternRewriter.addUsersInWorklist_same_ctx,
    hasUses!_oldVal_WfRewriter_replaceValue]

/-- `felt.add x (felt.const 0) → x`, fully sorry-free. The two defensive guards
    (`hRegNe`, `hEq`) supply the only two facts `WfIRContext` does not carry —
    `felt.add`'s region count and SSA acyclicity (result ≠ operand) — so the
    `eraseOp` preconditions discharge WITHOUT VEIR's `WfIRContext.Dom` axiom. The
    guards are sound: they only skip the rewrite in degenerate states impossible
    in well-formed IR. -/
def right_identity_zero_add (rewriter : PatternRewriter OpCode) (op : OperationPtr) :
    Option (PatternRewriter OpCode) := do
  match h : matchAdd op rewriter.ctx with
  | none => return rewriter
  | some (lhs, _rhs, _) =>
    let some rhsOp := _rhs.getDefiningOp! rewriter.ctx.raw | return rewriter
    let some cst := matchConst rhsOp rewriter.ctx | return rewriter
    if cst.value.value ≠ 0 then return rewriter
    -- Defensive guards for the two facts WfIRContext does not carry.
    if hRegNe : op.getNumRegions! rewriter.ctx.raw ≠ 0 then return rewriter else
    if hEq : (op.getResult 0 : ValuePtr) = lhs then return rewriter else
    have hReg0 : op.getNumRegions! rewriter.ctx.raw = 0 := by omega
    have hNe : (op.getResult 0 : ValuePtr) ≠ lhs := hEq
    -- Facts established from the match.
    have hIn : op.InBounds rewriter.ctx.raw := matchAdd_inBounds h
    have hWf : rewriter.ctx.raw.WellFormed := rewriter.ctx.wellFormed
    have hFib : rewriter.ctx.raw.FieldsInBounds := hWf.inBounds
    -- The guards inside `matchOp` must have passed for `matchAdd` to succeed, so `matchOp`
    -- returns `some (getOperands!, getProperties!)`.
    -- The `matchOp` inside `matchAdd` returned some value; its spec gives the operand/result
    -- counts, and `lhs` is operand 0.
    have key : op.getNumOperands! rewriter.ctx.raw = 2 ∧
        op.getNumResults! rewriter.ctx.raw = 1 ∧
        lhs = (op.getOperands! rewriter.ctx.raw)[0]! := by
      have h' := h
      simp only [matchAdd] at h'
      rcases hb : matchOp op rewriter.ctx.raw (OpCode.felt Felt.add) 2 with _ | ⟨o, p⟩
      · simp [hb] at h'
      · have hsp := matchOp_spec hb
        rw [hb] at h'
        simp only [bind, Option.bind, pure, Option.some.injEq, Prod.mk.injEq] at h'
        have hoeq : o = op.getOperands! rewriter.ctx.raw := by
          simp only [matchOp, bind, Option.bind, guard, pure] at hb; grind
        grind
    have hNumOps : op.getNumOperands! rewriter.ctx.raw = 2 := key.1
    have hNumRes : op.getNumResults! rewriter.ctx.raw = 1 := key.2.1
    have hLhsEq : lhs = (op.getOperands! rewriter.ctx.raw)[0]! := key.2.2
    -- Obligation #1: `(op.getResult 0).InBounds`.
    have hResIn : (op.getResult 0 : ValuePtr).InBounds rewriter.ctx.raw := by
      rw [ValuePtr.inBounds_opResult]
      exact op.getResult_inBounds hIn 0 (by grind)
    -- Obligation #2: `lhs.InBounds`. `lhs = (op.getOperands! ctx)[0]!`, a member of the
    -- operands array (size = numOperands = 2 > 0), hence in bounds.
    have hLhsMem : lhs ∈ op.getOperands! rewriter.ctx.raw := by
      have hsize : (op.getOperands! rewriter.ctx.raw).size = 2 := by
        rw [OperationPtr.getOperands!.size_eq_getNumOperands!]; exact hNumOps
      rw [hLhsEq, OperationPtr.getOperands!.getElem!_eq_getOperand!,
        ← OperationPtr.getOperands!.getElem_eq_getOperand! (h := by omega)]
      exact Array.getElem_mem (by omega)
    have hLhsIn : lhs.InBounds rewriter.ctx.raw :=
      OperationPtr.getOperands!_inBounds hFib hIn hLhsMem
    let rewriter' := rewriter.replaceValue (op.getResult 0) lhs hNe hResIn hLhsIn
    -- Obligation #3: `replaceValue` preserves region count, reducing to the pre-state count
    -- (which the matcher does not constrain — see report).
    have hRegions : op.getNumRegions! rewriter'.ctx.raw = op.getNumRegions! rewriter.ctx.raw :=
      getNumRegions!_replaceValue rewriter _ _ op hNe hResIn hLhsIn
    -- Obligation #5: `replaceValue` preserves `InBounds`.
    have hOpIn' : op.InBounds rewriter'.ctx.raw :=
      inBounds_replaceValue rewriter _ _ op hNe hResIn hLhsIn hIn
    -- Obligation #4: after replacing all uses of `op.getResult 0` by `lhs`, the (sole)
    -- result has no uses, hence neither does `op`.
    have hNumRes' : op.getNumResults! rewriter'.ctx.raw = 1 := by
      rw [getNumResults!_replaceValue rewriter _ _ op hNe hResIn hLhsIn]
      exact hNumRes
    have hNoUses : op.hasUses! rewriter'.ctx.raw = false := by
      rw [OperationPtr.hasUses!_eq_false_iff_hasUses!_getResult_eq_false]
      intro i hi
      rw [hNumRes'] at hi
      obtain rfl : i = 0 := by omega
      exact hasUses!_oldVal_replaceValue rewriter _ _ hResIn hLhsIn hNe
    -- eraseOp opRegions: via `hRegions` (replaceValue preserves region count) this
    -- reduces to the guarded `hReg0`.
    rewriter'.eraseOp op (hRegions.trans hReg0) (by simp [hNoUses]) hOpIn'

/-- The `PatternRewriter.createOp` postcondition, exposed as a relation between the raw
    contexts via `Rewriter.createOp`. -/
theorem createOp_post
    (rewriter rewriter' : PatternRewriter OpCode) (opType : OpCode)
    (resultTypes : Array TypeAttr) (operands : Array ValuePtr) (blockOperands : Array BlockPtr)
    (regions : Array RegionPtr) (properties : propertiesOf opType)
    (insertionPoint : Option InsertPoint) (newOp : OperationPtr)
    (hoper : ∀ oper, oper ∈ operands → oper.InBounds rewriter.ctx.raw)
    (hblockOperands : ∀ blockOper, blockOper ∈ blockOperands → blockOper.InBounds rewriter.ctx.raw)
    (hregions : ∀ region, region ∈ regions → region.InBounds rewriter.ctx.raw)
    (hins : insertionPoint.maybe InsertPoint.InBounds rewriter.ctx.raw)
    (h : rewriter.createOp opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (rewriter', newOp)) :
    ∃ h₅,
      Rewriter.createOp rewriter.ctx.raw opType resultTypes operands blockOperands regions
        properties insertionPoint hoper hblockOperands hregions hins h₅
        = some (rewriter'.ctx.raw, newOp) := by
  unfold PatternRewriter.createOp WfRewriter.createOp at h
  simp only [pure] at h
  -- The inner `Rewriter.createOp` either fails (contradiction) or yields `(ctx, op)`.
  split at h
  · -- inner createOp returned none
    rename_i hnone
    split at hnone <;> simp_all
  · rename_i newWfCtx newOp' hsome
    -- `hsome` reduces to the `Rewriter.createOp` result equation.
    split at hsome
    · simp at hsome
    · rename_i rawCtx op hcreate
      refine ⟨rewriter.ctx.wellFormed.inBounds, ?_⟩
      simp only [Option.some.injEq, Prod.mk.injEq] at hsome
      obtain ⟨hctxeq, hopeq⟩ := hsome
      -- Both branches of the `if insertionPoint.isNone` set `ctx := newWfCtx`.
      have hrw : rewriter'.ctx = newWfCtx ∧ newOp = newOp' := by
        split at h <;>
          (simp only [Option.some.injEq, Prod.mk.injEq] at h
           obtain ⟨h1, h2⟩ := h
           rw [← h1]; exact ⟨rfl, h2.symm⟩)
      rw [hcreate]
      simp only [Option.some.injEq, Prod.mk.injEq]
      refine ⟨?_, ?_⟩
      · rw [hrw.1, ← hctxeq]
      · rw [hrw.2, hopeq]

/-- `createOp` preserves `InBounds` of a pre-existing pointer. -/
theorem inBounds_createOp
    (rewriter rewriter' : PatternRewriter OpCode) (opType : OpCode)
    (resultTypes : Array TypeAttr) (operands : Array ValuePtr) (blockOperands : Array BlockPtr)
    (regions : Array RegionPtr) (properties : propertiesOf opType)
    (insertionPoint : Option InsertPoint) (newOp : OperationPtr) (ptr : GenericPtr)
    (hoper : ∀ oper, oper ∈ operands → oper.InBounds rewriter.ctx.raw)
    (hblockOperands : ∀ blockOper, blockOper ∈ blockOperands → blockOper.InBounds rewriter.ctx.raw)
    (hregions : ∀ region, region ∈ regions → region.InBounds rewriter.ctx.raw)
    (hins : insertionPoint.maybe InsertPoint.InBounds rewriter.ctx.raw)
    (hptr : ptr.InBounds rewriter.ctx.raw)
    (h : rewriter.createOp opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (rewriter', newOp)) :
    ptr.InBounds rewriter'.ctx.raw := by
  obtain ⟨h₅, hc⟩ := createOp_post rewriter rewriter' opType resultTypes operands blockOperands
    regions properties insertionPoint newOp hoper hblockOperands hregions hins h
  exact Rewriter.createOp_inBounds_mono ptr hc hptr

/-- The op returned by `createOp` is `InBounds` in the resulting context. -/
theorem newOp_inBounds_createOp
    (rewriter rewriter' : PatternRewriter OpCode) (opType : OpCode)
    (resultTypes : Array TypeAttr) (operands : Array ValuePtr) (blockOperands : Array BlockPtr)
    (regions : Array RegionPtr) (properties : propertiesOf opType)
    (insertionPoint : Option InsertPoint) (newOp : OperationPtr)
    (hoper : ∀ oper, oper ∈ operands → oper.InBounds rewriter.ctx.raw)
    (hblockOperands : ∀ blockOper, blockOper ∈ blockOperands → blockOper.InBounds rewriter.ctx.raw)
    (hregions : ∀ region, region ∈ regions → region.InBounds rewriter.ctx.raw)
    (hins : insertionPoint.maybe InsertPoint.InBounds rewriter.ctx.raw)
    (h : rewriter.createOp opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (rewriter', newOp)) :
    newOp.InBounds rewriter'.ctx.raw := by
  obtain ⟨h₅, hc⟩ := createOp_post rewriter rewriter' opType resultTypes operands blockOperands
    regions properties insertionPoint newOp hoper hblockOperands hregions hins h
  exact Rewriter.createOp_new_inBounds newOp hc

/-- The op returned by `createOp` was NOT `InBounds` in the pre-state: it is fresh. -/
theorem newOp_not_inBounds_pre_createOp
    (rewriter rewriter' : PatternRewriter OpCode) (opType : OpCode)
    (resultTypes : Array TypeAttr) (operands : Array ValuePtr) (blockOperands : Array BlockPtr)
    (regions : Array RegionPtr) (properties : propertiesOf opType)
    (insertionPoint : Option InsertPoint) (newOp : OperationPtr)
    (hoper : ∀ oper, oper ∈ operands → oper.InBounds rewriter.ctx.raw)
    (hblockOperands : ∀ blockOper, blockOper ∈ blockOperands → blockOper.InBounds rewriter.ctx.raw)
    (hregions : ∀ region, region ∈ regions → region.InBounds rewriter.ctx.raw)
    (hins : insertionPoint.maybe InsertPoint.InBounds rewriter.ctx.raw)
    (h : rewriter.createOp opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (rewriter', newOp)) :
    ¬ newOp.InBounds rewriter.ctx.raw := by
  obtain ⟨h₅, hc⟩ := createOp_post rewriter rewriter' opType resultTypes operands blockOperands
    regions properties insertionPoint newOp hoper hblockOperands hregions hins h
  exact Rewriter.createOp_new_not_inBounds newOp hc

/-- `createOp` is fresh: any op that is `InBounds` in the pre-state differs from the new op. -/
theorem opNe_createOp
    (rewriter rewriter' : PatternRewriter OpCode) (opType : OpCode)
    (resultTypes : Array TypeAttr) (operands : Array ValuePtr) (blockOperands : Array BlockPtr)
    (regions : Array RegionPtr) (properties : propertiesOf opType)
    (insertionPoint : Option InsertPoint) (newOp op : OperationPtr)
    (hoper : ∀ oper, oper ∈ operands → oper.InBounds rewriter.ctx.raw)
    (hblockOperands : ∀ blockOper, blockOper ∈ blockOperands → blockOper.InBounds rewriter.ctx.raw)
    (hregions : ∀ region, region ∈ regions → region.InBounds rewriter.ctx.raw)
    (hins : insertionPoint.maybe InsertPoint.InBounds rewriter.ctx.raw)
    (hOp : op.InBounds rewriter.ctx.raw)
    (h : rewriter.createOp opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (rewriter', newOp)) :
    op ≠ newOp := by
  intro heq
  subst heq
  exact newOp_not_inBounds_pre_createOp rewriter rewriter' opType resultTypes operands
    blockOperands regions properties insertionPoint op hoper hblockOperands hregions hins h hOp

/-- `createOp` preserves the region count of a pre-existing op (distinct from the new op). -/
theorem getNumRegions!_createOp
    (rewriter rewriter' : PatternRewriter OpCode) (opType : OpCode)
    (resultTypes : Array TypeAttr) (operands : Array ValuePtr) (blockOperands : Array BlockPtr)
    (regions : Array RegionPtr) (properties : propertiesOf opType)
    (insertionPoint : Option InsertPoint) (newOp op : OperationPtr)
    (hoper : ∀ oper, oper ∈ operands → oper.InBounds rewriter.ctx.raw)
    (hblockOperands : ∀ blockOper, blockOper ∈ blockOperands → blockOper.InBounds rewriter.ctx.raw)
    (hregions : ∀ region, region ∈ regions → region.InBounds rewriter.ctx.raw)
    (hins : insertionPoint.maybe InsertPoint.InBounds rewriter.ctx.raw)
    (hNe : op ≠ newOp)
    (h : rewriter.createOp opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (rewriter', newOp)) :
    op.getNumRegions! rewriter'.ctx.raw = op.getNumRegions! rewriter.ctx.raw := by
  obtain ⟨h₅, hc⟩ := createOp_post rewriter rewriter' opType resultTypes operands blockOperands
    regions properties insertionPoint newOp hoper hblockOperands hregions hins h
  rw [OperationPtr.getNumRegions!_createOp hc]
  simp [hNe]

/-- `createOp` preserves the `parent` field of a pre-existing op (distinct from the new op). -/
theorem parent_createOp
    (rewriter rewriter' : PatternRewriter OpCode) (opType : OpCode)
    (resultTypes : Array TypeAttr) (operands : Array ValuePtr) (blockOperands : Array BlockPtr)
    (regions : Array RegionPtr) (properties : propertiesOf opType)
    (insertionPoint : Option InsertPoint) (newOp op : OperationPtr)
    (hoper : ∀ oper, oper ∈ operands → oper.InBounds rewriter.ctx.raw)
    (hblockOperands : ∀ blockOper, blockOper ∈ blockOperands → blockOper.InBounds rewriter.ctx.raw)
    (hregions : ∀ region, region ∈ regions → region.InBounds rewriter.ctx.raw)
    (hins : insertionPoint.maybe InsertPoint.InBounds rewriter.ctx.raw)
    (hNe : op ≠ newOp)
    (h : rewriter.createOp opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (rewriter', newOp)) :
    (op.get! rewriter'.ctx.raw).parent = (op.get! rewriter.ctx.raw).parent := by
  obtain ⟨h₅, hc⟩ := createOp_post rewriter rewriter' opType resultTypes operands blockOperands
    regions properties insertionPoint newOp hoper hblockOperands hregions hins h
  rw [OperationPtr.parent!_createOp hc]
  simp [hNe]

/-- VEIR's real `constant_fold_add` rewrite (SHAPE 2: synthesize a new `felt.const` op,
    then `replaceOp`), fully sorry-free. The `createOp` preconditions discharge via the empty
    operand/region arrays plus `matchAdd_inBounds`. The `replaceOp` preconditions discharge via
    the `createOp` postcondition wrappers (`opNe_createOp`, `inBounds_createOp`,
    `newOp_inBounds_createOp`, `getNumRegions!_createOp`, `parent_createOp`) together with two
    defensive runtime guards supplying the only facts `WfIRContext` does not carry: `op`'s region
    count being `0` and `op` having a parent block. The guards are sound: they only skip the
    rewrite in degenerate states impossible for a well-formed matched `felt.add`. -/
def constant_fold_add (rewriter : PatternRewriter OpCode) (op : OperationPtr) :
    Option (PatternRewriter OpCode) := do
  match hm : matchAdd op rewriter.ctx with
  | none => return rewriter
  | some (lhs, rhs, _) =>
    let some cstL := matchConstFromValue lhs rewriter.ctx | return rewriter
    let some cstR := matchConstFromValue rhs rewriter.ctx | return rewriter
    if cstL.value.fieldType ≠ cstR.value.fieldType then return rewriter
    let some cstProp := foldedConstProperties? cstL.value.fieldType
      (cstL.value.value + cstR.value.value) | return rewriter
    let resultType := lhs.getType! rewriter.ctx.raw
    -- Defensive guards for the two facts `WfIRContext` does not carry about `op`.
    if hRegNe : op.getNumRegions! rewriter.ctx.raw ≠ 0 then return rewriter else
    if hPar : ¬ (op.get! rewriter.ctx.raw).parent.isSome then return rewriter else
    have hReg0 : op.getNumRegions! rewriter.ctx.raw = 0 := by omega
    have hParSome : (op.get! rewriter.ctx.raw).parent.isSome = true :=
      Decidable.not_not.mp hPar
    have hIn : op.InBounds rewriter.ctx.raw := matchAdd_inBounds hm
    -- `createOp` preconditions: empty arrays are trivially in-bounds; the insertion point
    -- `(.before op)` is in-bounds because `op` is.
    have hoper : ∀ oper, oper ∈ (#[] : Array ValuePtr) → oper.InBounds rewriter.ctx.raw := by
      simp
    have hblk : ∀ b, b ∈ (#[] : Array BlockPtr) → b.InBounds rewriter.ctx.raw := by simp
    have hreg : ∀ r, r ∈ (#[] : Array RegionPtr) → r.InBounds rewriter.ctx.raw := by simp
    have hins : (some (InsertPoint.before op)).maybe InsertPoint.InBounds rewriter.ctx.raw := by
      intro z hz
      simp only [Option.some.injEq] at hz
      subst hz
      rw [InsertPoint.inBounds_before]; exact hIn
    match hco : rewriter.createOp (OpCode.felt Felt.const) #[resultType] #[] #[] #[] cstProp
        (some (.before op)) hoper hblk hreg hins with
    | none => none
    | some (rewriter', newOp) =>
      -- `replaceOp` obligations, all from the `createOp` postcondition wrappers + guards.
      have hOpNe : op ≠ newOp :=
        opNe_createOp rewriter rewriter' _ _ _ _ _ _ _ newOp op hoper hblk hreg hins hIn hco
      have hPar' : (op.get! rewriter'.ctx.raw).parent.isSome = true := by
        rw [parent_createOp rewriter rewriter' _ _ _ _ _ _ _ newOp op hoper hblk hreg hins
          hOpNe hco]
        exact hParSome
      have hReg0' : op.getNumRegions! rewriter'.ctx.raw = 0 := by
        rw [getNumRegions!_createOp rewriter rewriter' _ _ _ _ _ _ _ newOp op hoper hblk hreg
          hins hOpNe hco]
        exact hReg0
      have hOpIn' : op.InBounds rewriter'.ctx.raw :=
        inBounds_createOp rewriter rewriter' _ _ _ _ _ _ _ newOp (GenericPtr.operation op)
          hoper hblk hreg hins hIn hco
      have hNewIn' : newOp.InBounds rewriter'.ctx.raw :=
        newOp_inBounds_createOp rewriter rewriter' _ _ _ _ _ _ _ newOp hoper hblk hreg hins hco
      rewriter'.replaceOp op newOp hOpNe hPar' hReg0' hOpIn' hNewIn'


/-! ## F1: 11 newly-verified Felt patterns (helpers + projection/synthesis tails) -/

theorem matchMul_spec {op : OperationPtr} {ctx : IRContext OpCode}
    {a b : ValuePtr} {p : propertiesOf (OpCode.felt Felt.mul)}
    (h : matchMul op ctx = some (a, b, p)) :
    op.getNumResults! ctx = 1 ∧ op.getNumOperands! ctx = 2 ∧
      a = (op.getOperands! ctx)[0]! ∧ b = (op.getOperands! ctx)[1]! := by
  unfold matchMul at h
  simp only [bind, Option.bind] at h
  split at h
  · simp at h
  · rename_i opair hb
    obtain ⟨oarr, oprop⟩ := opair
    have hsp := matchOp_spec hb
    have hoeq := matchOp_operands_eq hb
    obtain ⟨rfl, rfl, _⟩ := h
    exact ⟨hsp.2.2, hsp.2.1, by rw [hoeq], by rw [hoeq]⟩

theorem matchAdd_spec {op : OperationPtr} {ctx : IRContext OpCode}
    {a b : ValuePtr} {p : propertiesOf (OpCode.felt Felt.add)}
    (h : matchAdd op ctx = some (a, b, p)) :
    op.getNumResults! ctx = 1 ∧ op.getNumOperands! ctx = 2 ∧
      a = (op.getOperands! ctx)[0]! ∧ b = (op.getOperands! ctx)[1]! := by
  unfold matchAdd at h
  simp only [bind, Option.bind] at h
  split at h
  · simp at h
  · rename_i opair hb
    obtain ⟨oarr, oprop⟩ := opair
    have hsp := matchOp_spec hb
    have hoeq := matchOp_operands_eq hb
    obtain ⟨rfl, rfl, _⟩ := h
    exact ⟨hsp.2.2, hsp.2.1, by rw [hoeq], by rw [hoeq]⟩

theorem matchSub_spec {op : OperationPtr} {ctx : IRContext OpCode}
    {a b : ValuePtr} {p : propertiesOf (OpCode.felt Felt.sub)}
    (h : matchSub op ctx = some (a, b, p)) :
    op.getNumResults! ctx = 1 ∧ op.getNumOperands! ctx = 2 ∧
      a = (op.getOperands! ctx)[0]! ∧ b = (op.getOperands! ctx)[1]! := by
  unfold matchSub at h
  simp only [bind, Option.bind] at h
  split at h
  · simp at h
  · rename_i opair hb
    obtain ⟨oarr, oprop⟩ := opair
    have hsp := matchOp_spec hb
    have hoeq := matchOp_operands_eq hb
    obtain ⟨rfl, rfl, _⟩ := h
    exact ⟨hsp.2.2, hsp.2.1, by rw [hoeq], by rw [hoeq]⟩

theorem matchNeg_spec {op : OperationPtr} {ctx : IRContext OpCode}
    {a : ValuePtr} {p : propertiesOf (OpCode.felt Felt.neg)}
    (h : matchNeg op ctx = some (a, p)) :
    op.getNumResults! ctx = 1 ∧ op.getNumOperands! ctx = 1 ∧
      a = (op.getOperands! ctx)[0]! := by
  unfold matchNeg at h
  simp only [bind, Option.bind] at h
  split at h
  · simp at h
  · rename_i opair hb
    obtain ⟨oarr, oprop⟩ := opair
    have hsp := matchOp_spec hb
    have hoeq := matchOp_operands_eq hb
    obtain ⟨rfl, _⟩ := h
    exact ⟨hsp.2.2, hsp.2.1, by rw [hoeq]⟩

/-- Reusable projection tail: given a matched, in-bounds op with a single result, region
    count 0, and an in-bounds replacement `target` distinct from the result, replace all uses
    of `op`'s result by `target` and erase `op`. All `replaceValue`/`eraseOp` preconditions
    discharge from the supplied facts (no `WfIRContext.Dom`). -/
def projectToOperand (rewriter : PatternRewriter OpCode) (op : OperationPtr) (target : ValuePtr)
    (hIn : op.InBounds rewriter.ctx.raw)
    (hReg0 : op.getNumRegions! rewriter.ctx.raw = 0)
    (hNumRes : op.getNumResults! rewriter.ctx.raw = 1)
    (hNe : (op.getResult 0 : ValuePtr) ≠ target)
    (hResIn : (op.getResult 0 : ValuePtr).InBounds rewriter.ctx.raw)
    (hTgtIn : target.InBounds rewriter.ctx.raw) :
    Option (PatternRewriter OpCode) :=
  let rewriter' := rewriter.replaceValue (op.getResult 0) target hNe hResIn hTgtIn
  have hRegions : op.getNumRegions! rewriter'.ctx.raw = op.getNumRegions! rewriter.ctx.raw :=
    getNumRegions!_replaceValue rewriter _ _ op hNe hResIn hTgtIn
  have hOpIn' : op.InBounds rewriter'.ctx.raw :=
    inBounds_replaceValue rewriter _ _ op hNe hResIn hTgtIn hIn
  have hNumRes' : op.getNumResults! rewriter'.ctx.raw = 1 := by
    rw [getNumResults!_replaceValue rewriter _ _ op hNe hResIn hTgtIn]
    exact hNumRes
  have hNoUses : op.hasUses! rewriter'.ctx.raw = false := by
    rw [OperationPtr.hasUses!_eq_false_iff_hasUses!_getResult_eq_false]
    intro i hi
    rw [hNumRes'] at hi
    obtain rfl : i = 0 := by omega
    exact hasUses!_oldVal_replaceValue rewriter _ _ hResIn hTgtIn hNe
  rewriter'.eraseOp op (hRegions.trans hReg0) (by simp [hNoUses]) hOpIn'

/-- The neg-operand reached through `matchNegFromValue` is in bounds. -/
theorem matchNegFromValue_operand0_inBounds {val : ValuePtr} {ctx : IRContext OpCode}
    {a : ValuePtr} {p : propertiesOf (OpCode.felt Felt.neg)}
    (hFib : ctx.FieldsInBounds) (h : matchNegFromValue val ctx = some (a, p)) :
    a.InBounds ctx := by
  unfold matchNegFromValue at h
  split at h
  · have hInnerIn := matchNeg_inBounds h
    have hsp := matchNeg_spec h
    rw [hsp.2.2]; exact getOperand_inBounds hFib hInnerIn 0 (by rw [hsp.2.1]; omega)
  · simp at h

/-- Operand 0 (the `x`) reached through `matchAddFromValue` is in bounds. -/
theorem matchAddFromValue_operand0_inBounds {val : ValuePtr} {ctx : IRContext OpCode}
    {a b : ValuePtr} {p : propertiesOf (OpCode.felt Felt.add)}
    (hFib : ctx.FieldsInBounds) (h : matchAddFromValue val ctx = some (a, b, p)) :
    a.InBounds ctx := by
  unfold matchAddFromValue at h
  split at h
  · have hInnerIn := matchAdd_inBounds h
    have hsp := matchAdd_spec h
    rw [hsp.2.2.1]; exact getOperand_inBounds hFib hInnerIn 0 (by rw [hsp.2.1]; omega)
  · simp at h

/-- Operand 0 (the `x`) reached through `matchSubFromValue` is in bounds. -/
theorem matchSubFromValue_operand0_inBounds {val : ValuePtr} {ctx : IRContext OpCode}
    {a b : ValuePtr} {p : propertiesOf (OpCode.felt Felt.sub)}
    (hFib : ctx.FieldsInBounds) (h : matchSubFromValue val ctx = some (a, b, p)) :
    a.InBounds ctx := by
  unfold matchSubFromValue at h
  split at h
  · have hInnerIn := matchSub_inBounds h
    have hsp := matchSub_spec h
    rw [hsp.2.2.1]; exact getOperand_inBounds hFib hInnerIn 0 (by rw [hsp.2.1]; omega)
  · simp at h

/-- Reusable synthesis tail: create a single new op (`opType` with the given result types,
    operands and properties, no block-operands/regions) positioned before `op`, then replace
    `op` by it. All `createOp`/`replaceOp` preconditions discharge from the supplied facts
    (region count 0 and `op` having a parent — the two facts `WfIRContext` does not carry — plus
    operand in-bounds). No `WfIRContext.Dom`. -/
def replaceWithNewOp (rewriter : PatternRewriter OpCode) (op : OperationPtr) (opType : OpCode)
    (resultTypes : Array TypeAttr) (operands : Array ValuePtr) (properties : propertiesOf opType)
    (hIn : op.InBounds rewriter.ctx.raw)
    (hReg0 : op.getNumRegions! rewriter.ctx.raw = 0)
    (hParSome : (op.get! rewriter.ctx.raw).parent.isSome = true)
    (hoper : ∀ oper, oper ∈ operands → oper.InBounds rewriter.ctx.raw) :
    Option (PatternRewriter OpCode) :=
  have hblk : ∀ b, b ∈ (#[] : Array BlockPtr) → b.InBounds rewriter.ctx.raw := by simp
  have hreg : ∀ r, r ∈ (#[] : Array RegionPtr) → r.InBounds rewriter.ctx.raw := by simp
  have hins : (some (InsertPoint.before op)).maybe InsertPoint.InBounds rewriter.ctx.raw := by
    intro z hz
    simp only [Option.some.injEq] at hz
    subst hz
    rw [InsertPoint.inBounds_before]; exact hIn
  match hco : rewriter.createOp opType resultTypes operands #[] #[] properties
      (some (.before op)) hoper hblk hreg hins with
  | none => none
  | some (rewriter', newOp) =>
    have hOpNe : op ≠ newOp :=
      opNe_createOp rewriter rewriter' _ _ _ _ _ _ _ newOp op hoper hblk hreg hins hIn hco
    have hPar' : (op.get! rewriter'.ctx.raw).parent.isSome = true := by
      rw [parent_createOp rewriter rewriter' _ _ _ _ _ _ _ newOp op hoper hblk hreg hins
        hOpNe hco]
      exact hParSome
    have hReg0' : op.getNumRegions! rewriter'.ctx.raw = 0 := by
      rw [getNumRegions!_createOp rewriter rewriter' _ _ _ _ _ _ _ newOp op hoper hblk hreg
        hins hOpNe hco]
      exact hReg0
    have hOpIn' : op.InBounds rewriter'.ctx.raw :=
      inBounds_createOp rewriter rewriter' _ _ _ _ _ _ _ newOp (GenericPtr.operation op)
        hoper hblk hreg hins hIn hco
    have hNewIn' : newOp.InBounds rewriter'.ctx.raw :=
      newOp_inBounds_createOp rewriter rewriter' _ _ _ _ _ _ _ newOp hoper hblk hreg hins hco
    rewriter'.replaceOp op newOp hOpNe hPar' hReg0' hOpIn' hNewIn'

/-- felt.mul x (felt.const 1) → x.  Soundness: `right_identity_one_mul`. -/
def right_identity_one_mul (rewriter : PatternRewriter OpCode) (op : OperationPtr) :
    Option (PatternRewriter OpCode) := do
  match h : matchMul op rewriter.ctx with
  | none => return rewriter
  | some (lhs, rhs, _) =>
    let some rhsOp := rhs.getDefiningOp! rewriter.ctx.raw | return rewriter
    let some cst := matchConst rhsOp rewriter.ctx | return rewriter
    if cst.value.value ≠ 1 then return rewriter
    if hRegNe : op.getNumRegions! rewriter.ctx.raw ≠ 0 then return rewriter else
    if hEq : (op.getResult 0 : ValuePtr) = lhs then return rewriter else
    have hReg0 : op.getNumRegions! rewriter.ctx.raw = 0 := by omega
    have hIn : op.InBounds rewriter.ctx.raw := matchMul_inBounds h
    have hFib : rewriter.ctx.raw.FieldsInBounds := rewriter.ctx.wellFormed.inBounds
    have hsp := matchMul_spec h
    have hNumRes : op.getNumResults! rewriter.ctx.raw = 1 := hsp.1
    have hResIn := getResult0_inBounds hIn hNumRes
    have hLhsIn : lhs.InBounds rewriter.ctx.raw := by
      rw [hsp.2.2.1]; exact getOperand_inBounds hFib hIn 0 (by rw [hsp.2.1]; omega)
    projectToOperand rewriter op lhs hIn hReg0 hNumRes hEq hResIn hLhsIn

/-- felt.sub (felt.const c1) (felt.const c2) → felt.const (c1-c2). -/
def constant_fold_sub (rewriter : PatternRewriter OpCode) (op : OperationPtr) :
    Option (PatternRewriter OpCode) := do
  match h : matchSub op rewriter.ctx with
  | none => return rewriter
  | some (lhs, rhs, _) =>
    let some cstL := matchConstFromValue lhs rewriter.ctx | return rewriter
    let some cstR := matchConstFromValue rhs rewriter.ctx | return rewriter
    if cstL.value.fieldType ≠ cstR.value.fieldType then return rewriter
    let some cstProp := foldedConstProperties? cstL.value.fieldType
      (cstL.value.value - cstR.value.value) | return rewriter
    let resultType := lhs.getType! rewriter.ctx.raw
    if hRegNe : op.getNumRegions! rewriter.ctx.raw ≠ 0 then return rewriter else
    if hPar : ¬ (op.get! rewriter.ctx.raw).parent.isSome then return rewriter else
    have hReg0 : op.getNumRegions! rewriter.ctx.raw = 0 := by omega
    have hParSome := Decidable.not_not.mp hPar
    have hIn : op.InBounds rewriter.ctx.raw := matchSub_inBounds h
    replaceWithNewOp rewriter op (OpCode.felt Felt.const) #[resultType] #[] cstProp
      hIn hReg0 hParSome (by simp)

/-- felt.mul (felt.const c1) (felt.const c2) → felt.const (c1*c2). -/
def constant_fold_mul (rewriter : PatternRewriter OpCode) (op : OperationPtr) :
    Option (PatternRewriter OpCode) := do
  match h : matchMul op rewriter.ctx with
  | none => return rewriter
  | some (lhs, rhs, _) =>
    let some cstL := matchConstFromValue lhs rewriter.ctx | return rewriter
    let some cstR := matchConstFromValue rhs rewriter.ctx | return rewriter
    if cstL.value.fieldType ≠ cstR.value.fieldType then return rewriter
    let some cstProp := foldedConstProperties? cstL.value.fieldType
      (cstL.value.value * cstR.value.value) | return rewriter
    let resultType := lhs.getType! rewriter.ctx.raw
    if hRegNe : op.getNumRegions! rewriter.ctx.raw ≠ 0 then return rewriter else
    if hPar : ¬ (op.get! rewriter.ctx.raw).parent.isSome then return rewriter else
    have hReg0 : op.getNumRegions! rewriter.ctx.raw = 0 := by omega
    have hParSome := Decidable.not_not.mp hPar
    have hIn : op.InBounds rewriter.ctx.raw := matchMul_inBounds h
    replaceWithNewOp rewriter op (OpCode.felt Felt.const) #[resultType] #[] cstProp
      hIn hReg0 hParSome (by simp)

/-- felt.neg (felt.const c) → felt.const (-c). -/
def constant_fold_neg (rewriter : PatternRewriter OpCode) (op : OperationPtr) :
    Option (PatternRewriter OpCode) := do
  match h : matchNeg op rewriter.ctx with
  | none => return rewriter
  | some (operand, _) =>
    let some cst := matchConstFromValue operand rewriter.ctx | return rewriter
    let some cstProp := foldedConstProperties? cst.value.fieldType (-cst.value.value) |
      return rewriter
    let resultType := operand.getType! rewriter.ctx.raw
    if hRegNe : op.getNumRegions! rewriter.ctx.raw ≠ 0 then return rewriter else
    if hPar : ¬ (op.get! rewriter.ctx.raw).parent.isSome then return rewriter else
    have hReg0 : op.getNumRegions! rewriter.ctx.raw = 0 := by omega
    have hParSome := Decidable.not_not.mp hPar
    have hIn : op.InBounds rewriter.ctx.raw := matchNeg_inBounds h
    replaceWithNewOp rewriter op (OpCode.felt Felt.const) #[resultType] #[] cstProp
      hIn hReg0 hParSome (by simp)

/-- felt.sub x x → felt.const 0. -/
def self_subtraction_to_zero (rewriter : PatternRewriter OpCode) (op : OperationPtr) :
    Option (PatternRewriter OpCode) := do
  match h : matchSub op rewriter.ctx with
  | none => return rewriter
  | some (lhs, rhs, _) =>
    if lhs ≠ rhs then return rewriter
    let resultType := lhs.getType! rewriter.ctx.raw
    let Attribute.feltType ft := resultType.val | return rewriter
    let cstProp : FeltConstProperties := { value := { value := 0, fieldType := ft } }
    if hRegNe : op.getNumRegions! rewriter.ctx.raw ≠ 0 then return rewriter else
    if hPar : ¬ (op.get! rewriter.ctx.raw).parent.isSome then return rewriter else
    have hReg0 : op.getNumRegions! rewriter.ctx.raw = 0 := by omega
    have hParSome := Decidable.not_not.mp hPar
    have hIn : op.InBounds rewriter.ctx.raw := matchSub_inBounds h
    replaceWithNewOp rewriter op (OpCode.felt Felt.const) #[resultType] #[] cstProp
      hIn hReg0 hParSome (by simp)

/-- felt.mul x (felt.const 0) → felt.const 0.  Soundness: `right_zero_mul`. -/
def right_zero_mul (rewriter : PatternRewriter OpCode) (op : OperationPtr) :
    Option (PatternRewriter OpCode) := do
  match h : matchMul op rewriter.ctx with
  | none => return rewriter
  | some (lhs, rhs, _) =>
    let some rhsOp := rhs.getDefiningOp! rewriter.ctx.raw | return rewriter
    let some cst := matchConst rhsOp rewriter.ctx | return rewriter
    if cst.value.value ≠ 0 then return rewriter
    let resultType := lhs.getType! rewriter.ctx.raw
    let Attribute.feltType ft := resultType.val | return rewriter
    let cstProp : FeltConstProperties := { value := { value := 0, fieldType := ft } }
    if hRegNe : op.getNumRegions! rewriter.ctx.raw ≠ 0 then return rewriter else
    if hPar : ¬ (op.get! rewriter.ctx.raw).parent.isSome then return rewriter else
    have hReg0 : op.getNumRegions! rewriter.ctx.raw = 0 := by omega
    have hParSome := Decidable.not_not.mp hPar
    have hIn : op.InBounds rewriter.ctx.raw := matchMul_inBounds h
    replaceWithNewOp rewriter op (OpCode.felt Felt.const) #[resultType] #[] cstProp
      hIn hReg0 hParSome (by simp)

/-- felt.add x (felt.neg x) → felt.const 0.  Soundness: `add_neg_to_zero`. -/
def add_neg_to_zero (rewriter : PatternRewriter OpCode) (op : OperationPtr) :
    Option (PatternRewriter OpCode) := do
  match h : matchAdd op rewriter.ctx with
  | none => return rewriter
  | some (lhs, rhs, _) =>
    let some (innerVal, _) := matchNegFromValue rhs rewriter.ctx | return rewriter
    if lhs ≠ innerVal then return rewriter
    let resultType := lhs.getType! rewriter.ctx.raw
    let Attribute.feltType ft := resultType.val | return rewriter
    let cstProp : FeltConstProperties := { value := { value := 0, fieldType := ft } }
    if hRegNe : op.getNumRegions! rewriter.ctx.raw ≠ 0 then return rewriter else
    if hPar : ¬ (op.get! rewriter.ctx.raw).parent.isSome then return rewriter else
    have hReg0 : op.getNumRegions! rewriter.ctx.raw = 0 := by omega
    have hParSome := Decidable.not_not.mp hPar
    have hIn : op.InBounds rewriter.ctx.raw := matchAdd_inBounds h
    replaceWithNewOp rewriter op (OpCode.felt Felt.const) #[resultType] #[] cstProp
      hIn hReg0 hParSome (by simp)

/-- felt.add (felt.const c) x → felt.add x (felt.const c).  Soundness: `add_const_swap`. -/
def add_const_swap (rewriter : PatternRewriter OpCode) (op : OperationPtr) :
    Option (PatternRewriter OpCode) := do
  match h : matchAdd op rewriter.ctx with
  | none => return rewriter
  | some (lhs, rhs, _) =>
    let some _ := matchConstFromValue lhs rewriter.ctx | return rewriter
    if (matchConstFromValue rhs rewriter.ctx).isSome then return rewriter
    let resultType := lhs.getType! rewriter.ctx.raw
    if hRegNe : op.getNumRegions! rewriter.ctx.raw ≠ 0 then return rewriter else
    if hPar : ¬ (op.get! rewriter.ctx.raw).parent.isSome then return rewriter else
    have hReg0 : op.getNumRegions! rewriter.ctx.raw = 0 := by omega
    have hParSome := Decidable.not_not.mp hPar
    have hIn : op.InBounds rewriter.ctx.raw := matchAdd_inBounds h
    have hFib : rewriter.ctx.raw.FieldsInBounds := rewriter.ctx.wellFormed.inBounds
    have hsp := matchAdd_spec h
    have hLhsIn : lhs.InBounds rewriter.ctx.raw := by
      rw [hsp.2.2.1]; exact getOperand_inBounds hFib hIn 0 (by rw [hsp.2.1]; omega)
    have hRhsIn : rhs.InBounds rewriter.ctx.raw := by
      rw [hsp.2.2.2]; exact getOperand_inBounds hFib hIn 1 (by rw [hsp.2.1]; omega)
    replaceWithNewOp rewriter op (OpCode.felt Felt.add) #[resultType] #[rhs, lhs] ()
      hIn hReg0 hParSome (by
        intro oper hoper
        rw [Array.mem_def] at hoper
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hoper
        rcases hoper with rfl | rfl
        · exact hRhsIn
        · exact hLhsIn)

/-- felt.neg (felt.neg x) → x.  Soundness: `neg_neg_to_self`. -/
def neg_neg_to_self (rewriter : PatternRewriter OpCode) (op : OperationPtr) :
    Option (PatternRewriter OpCode) := do
  match h : matchNeg op rewriter.ctx with
  | none => return rewriter
  | some (operand, _) =>
    match hInner : matchNegFromValue operand rewriter.ctx with
    | none => return rewriter
    | some (inner, _) =>
      if hRegNe : op.getNumRegions! rewriter.ctx.raw ≠ 0 then return rewriter else
      if hEq : (op.getResult 0 : ValuePtr) = inner then return rewriter else
      have hReg0 : op.getNumRegions! rewriter.ctx.raw = 0 := by omega
      have hIn : op.InBounds rewriter.ctx.raw := matchNeg_inBounds h
      have hFib : rewriter.ctx.raw.FieldsInBounds := rewriter.ctx.wellFormed.inBounds
      have hNumRes : op.getNumResults! rewriter.ctx.raw = 1 := (matchNeg_spec h).1
      have hResIn := getResult0_inBounds hIn hNumRes
      have hInnerIn := matchNegFromValue_operand0_inBounds hFib hInner
      projectToOperand rewriter op inner hIn hReg0 hNumRes hEq hResIn hInnerIn

/-- felt.sub (felt.add x c) c → x.  Soundness: `add_sub_const_cancel`. -/
def add_sub_const_cancel (rewriter : PatternRewriter OpCode) (op : OperationPtr) :
    Option (PatternRewriter OpCode) := do
  match h : matchSub op rewriter.ctx with
  | none => return rewriter
  | some (innerVal, outerC, _) =>
    let some outerCst := matchConstFromValue outerC rewriter.ctx | return rewriter
    match hInner : matchAddFromValue innerVal rewriter.ctx with
    | none => return rewriter
    | some (x, innerC, _) =>
      let some innerCst := matchConstFromValue innerC rewriter.ctx | return rewriter
      if innerCst.value.value ≠ outerCst.value.value then return rewriter
      if hRegNe : op.getNumRegions! rewriter.ctx.raw ≠ 0 then return rewriter else
      if hEq : (op.getResult 0 : ValuePtr) = x then return rewriter else
      have hReg0 : op.getNumRegions! rewriter.ctx.raw = 0 := by omega
      have hIn : op.InBounds rewriter.ctx.raw := matchSub_inBounds h
      have hFib : rewriter.ctx.raw.FieldsInBounds := rewriter.ctx.wellFormed.inBounds
      have hNumRes : op.getNumResults! rewriter.ctx.raw = 1 := (matchSub_spec h).1
      have hResIn := getResult0_inBounds hIn hNumRes
      have hXIn := matchAddFromValue_operand0_inBounds hFib hInner
      projectToOperand rewriter op x hIn hReg0 hNumRes hEq hResIn hXIn

/-- felt.add (felt.sub x c) c → x.  Soundness: `sub_add_const_cancel`. -/
def sub_add_const_cancel (rewriter : PatternRewriter OpCode) (op : OperationPtr) :
    Option (PatternRewriter OpCode) := do
  match h : matchAdd op rewriter.ctx with
  | none => return rewriter
  | some (innerVal, outerC, _) =>
    let some outerCst := matchConstFromValue outerC rewriter.ctx | return rewriter
    match hInner : matchSubFromValue innerVal rewriter.ctx with
    | none => return rewriter
    | some (x, innerC, _) =>
      let some innerCst := matchConstFromValue innerC rewriter.ctx | return rewriter
      if innerCst.value.value ≠ outerCst.value.value then return rewriter
      if hRegNe : op.getNumRegions! rewriter.ctx.raw ≠ 0 then return rewriter else
      if hEq : (op.getResult 0 : ValuePtr) = x then return rewriter else
      have hReg0 : op.getNumRegions! rewriter.ctx.raw = 0 := by omega
      have hIn : op.InBounds rewriter.ctx.raw := matchAdd_inBounds h
      have hFib : rewriter.ctx.raw.FieldsInBounds := rewriter.ctx.wellFormed.inBounds
      have hNumRes : op.getNumResults! rewriter.ctx.raw = 1 := (matchAdd_spec h).1
      have hResIn := getResult0_inBounds hIn hNumRes
      have hXIn := matchSubFromValue_operand0_inBounds hFib hInner
      projectToOperand rewriter op x hIn hReg0 hNumRes hEq hResIn hXIn



/-! ## F1: the two associativity folds (createOp-then-createOp composition) -/

/-- Operand 0 (the `x`) reached through `matchMulFromValue` is in bounds. -/
theorem matchMulFromValue_operand0_inBounds {val : ValuePtr} {ctx : IRContext OpCode}
    {a b : ValuePtr} {p : propertiesOf (OpCode.felt Felt.mul)}
    (hFib : ctx.FieldsInBounds) (h : matchMulFromValue val ctx = some (a, b, p)) :
    a.InBounds ctx := by
  unfold matchMulFromValue at h
  split at h
  · have hInnerIn := matchMul_inBounds h
    have hsp := matchMul_spec h
    rw [hsp.2.2.1]; exact getOperand_inBounds hFib hInnerIn 0 (by rw [hsp.2.1]; omega)
  · simp at h


/-- The op produced by `createOp` has exactly `resultTypes.size` results. -/
theorem newOp_getNumResults!_createOp
    (rewriter rewriter' : PatternRewriter OpCode) (opType : OpCode)
    (resultTypes : Array TypeAttr) (operands : Array ValuePtr) (blockOperands : Array BlockPtr)
    (regions : Array RegionPtr) (properties : propertiesOf opType)
    (insertionPoint : Option InsertPoint) (newOp : OperationPtr)
    (hoper : ∀ oper, oper ∈ operands → oper.InBounds rewriter.ctx.raw)
    (hblockOperands : ∀ blockOper, blockOper ∈ blockOperands → blockOper.InBounds rewriter.ctx.raw)
    (hregions : ∀ region, region ∈ regions → region.InBounds rewriter.ctx.raw)
    (hins : insertionPoint.maybe InsertPoint.InBounds rewriter.ctx.raw)
    (h : rewriter.createOp opType resultTypes operands blockOperands regions properties
      insertionPoint hoper hblockOperands hregions hins = some (rewriter', newOp)) :
    newOp.getNumResults! rewriter'.ctx.raw = resultTypes.size := by
  obtain ⟨h₅, hc⟩ := createOp_post rewriter rewriter' opType resultTypes operands blockOperands
    regions properties insertionPoint newOp hoper hblockOperands hregions hins h
  rw [OperationPtr.getNumResults!_createOp hc]; simp

/-- Reusable two-op synthesis tail: synthesize a `felt.const` (`cstProp`/`resultType`), then a
    binary op `binOpType #[x, <that const>]`, then replace `op` by the binary op. Used by the
    associativity folds, which rewrite `(x ∘ c1) ∘ c2 → x ∘ (c1∘c2)`. `x` and the fresh const's
    result are in bounds for the second `createOp` (the first `createOp` preserves `x` and freshly
    creates the const with one result); all preconditions discharge from the supplied facts +
    the `createOp` postcondition wrappers. No `WfIRContext.Dom`. -/
def replaceWithBinOpOfConst (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (binOpType : OpCode) (binProp : propertiesOf binOpType) (resultType : TypeAttr)
    (x : ValuePtr) (cstProp : FeltConstProperties)
    (hIn : op.InBounds rewriter.ctx.raw)
    (hReg0 : op.getNumRegions! rewriter.ctx.raw = 0)
    (hParSome : (op.get! rewriter.ctx.raw).parent.isSome = true)
    (hxIn : x.InBounds rewriter.ctx.raw) :
    Option (PatternRewriter OpCode) :=
  have hoperC : ∀ oper, oper ∈ (#[] : Array ValuePtr) → oper.InBounds rewriter.ctx.raw := by simp
  have hblk : ∀ b, b ∈ (#[] : Array BlockPtr) → b.InBounds rewriter.ctx.raw := by simp
  have hreg : ∀ r, r ∈ (#[] : Array RegionPtr) → r.InBounds rewriter.ctx.raw := by simp
  have hins : (some (InsertPoint.before op)).maybe InsertPoint.InBounds rewriter.ctx.raw := by
    intro z hz
    simp only [Option.some.injEq] at hz
    subst hz
    rw [InsertPoint.inBounds_before]; exact hIn
  match hco : rewriter.createOp (OpCode.felt Felt.const) #[resultType] #[] #[] #[] cstProp
      (some (.before op)) hoperC hblk hreg hins with
  | none => none
  | some (r1, constOp) =>
    have hOpNe : op ≠ constOp :=
      opNe_createOp rewriter r1 _ _ _ _ _ _ _ constOp op hoperC hblk hreg hins hIn hco
    have hParSome1 : (op.get! r1.ctx.raw).parent.isSome = true := by
      rw [parent_createOp rewriter r1 _ _ _ _ _ _ _ constOp op hoperC hblk hreg hins hOpNe hco]
      exact hParSome
    have hReg01 : op.getNumRegions! r1.ctx.raw = 0 := by
      rw [getNumRegions!_createOp rewriter r1 _ _ _ _ _ _ _ constOp op hoperC hblk hreg hins
        hOpNe hco]
      exact hReg0
    have hOpIn1 : op.InBounds r1.ctx.raw :=
      inBounds_createOp rewriter r1 _ _ _ _ _ _ _ constOp (GenericPtr.operation op)
        hoperC hblk hreg hins hIn hco
    have hxIn1 : x.InBounds r1.ctx.raw :=
      inBounds_createOp rewriter r1 _ _ _ _ _ _ _ constOp (GenericPtr.value x)
        hoperC hblk hreg hins hxIn hco
    have hConstIn1 : constOp.InBounds r1.ctx.raw :=
      newOp_inBounds_createOp rewriter r1 _ _ _ _ _ _ _ constOp hoperC hblk hreg hins hco
    have hConstRes1 : constOp.getNumResults! r1.ctx.raw = 1 := by
      rw [newOp_getNumResults!_createOp rewriter r1 _ _ _ _ _ _ _ constOp hoperC hblk hreg hins
        hco]; simp
    have hConstResIn1 : (constOp.getResult 0 : ValuePtr).InBounds r1.ctx.raw :=
      getResult0_inBounds hConstIn1 hConstRes1
    replaceWithNewOp r1 op binOpType #[resultType] #[x, constOp.getResult 0] binProp
      hOpIn1 hReg01 hParSome1 (by
        intro oper hoper
        rw [Array.mem_def] at hoper
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hoper
        rcases hoper with rfl | rfl
        · exact hxIn1
        · exact hConstResIn1)

/-- felt.add (felt.add x c1) c2 → felt.add x (c1+c2). -/
def assoc_const_fold_add (rewriter : PatternRewriter OpCode) (op : OperationPtr) :
    Option (PatternRewriter OpCode) := do
  match h : matchAdd op rewriter.ctx with
  | none => return rewriter
  | some (innerVal, c2Val, _) =>
    let some c2 := matchConstFromValue c2Val rewriter.ctx | return rewriter
    match hInner : matchAddFromValue innerVal rewriter.ctx with
    | none => return rewriter
    | some (x, c1Val, _) =>
      let some c1 := matchConstFromValue c1Val rewriter.ctx | return rewriter
      if c1.value.fieldType ≠ c2.value.fieldType then return rewriter
      let some combinedCst := foldedConstProperties? c1.value.fieldType
        (c1.value.value + c2.value.value) | return rewriter
      let resultType := x.getType! rewriter.ctx.raw
      if hRegNe : op.getNumRegions! rewriter.ctx.raw ≠ 0 then return rewriter else
      if hPar : ¬ (op.get! rewriter.ctx.raw).parent.isSome then return rewriter else
      have hReg0 : op.getNumRegions! rewriter.ctx.raw = 0 := by omega
      have hParSome := Decidable.not_not.mp hPar
      have hIn : op.InBounds rewriter.ctx.raw := matchAdd_inBounds h
      have hFib : rewriter.ctx.raw.FieldsInBounds := rewriter.ctx.wellFormed.inBounds
      have hxIn := matchAddFromValue_operand0_inBounds hFib hInner
      replaceWithBinOpOfConst rewriter op (OpCode.felt Felt.add) () resultType x combinedCst
        hIn hReg0 hParSome hxIn

/-- felt.mul (felt.mul x c1) c2 → felt.mul x (c1*c2). -/
def assoc_const_fold_mul (rewriter : PatternRewriter OpCode) (op : OperationPtr) :
    Option (PatternRewriter OpCode) := do
  match h : matchMul op rewriter.ctx with
  | none => return rewriter
  | some (innerVal, c2Val, _) =>
    let some c2 := matchConstFromValue c2Val rewriter.ctx | return rewriter
    match hInner : matchMulFromValue innerVal rewriter.ctx with
    | none => return rewriter
    | some (x, c1Val, _) =>
      let some c1 := matchConstFromValue c1Val rewriter.ctx | return rewriter
      if c1.value.fieldType ≠ c2.value.fieldType then return rewriter
      let some combinedCst := foldedConstProperties? c1.value.fieldType
        (c1.value.value * c2.value.value) | return rewriter
      let resultType := x.getType! rewriter.ctx.raw
      if hRegNe : op.getNumRegions! rewriter.ctx.raw ≠ 0 then return rewriter else
      if hPar : ¬ (op.get! rewriter.ctx.raw).parent.isSome then return rewriter else
      have hReg0 : op.getNumRegions! rewriter.ctx.raw = 0 := by omega
      have hParSome := Decidable.not_not.mp hPar
      have hIn : op.InBounds rewriter.ctx.raw := matchMul_inBounds h
      have hFib : rewriter.ctx.raw.FieldsInBounds := rewriter.ctx.wellFormed.inBounds
      have hxIn := matchMulFromValue_operand0_inBounds hFib hInner
      replaceWithBinOpOfConst rewriter op (OpCode.felt Felt.mul) () resultType x combinedCst
        hIn hReg0 hParSome hxIn

end FeltPass
end Veir
