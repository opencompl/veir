import Veir.Passes.Matching
import Veir.Passes.Felt.Matching

namespace Veir

theorem matchOp_spec {op : OperationPtr} {ctx : IRContext OpCode} {opType : OpCode}
    {n : Nat} {r : Array ValuePtr × propertiesOf opType}
    (h : matchOp op ctx opType n = some r) :
    op.getOpType! ctx = opType ∧ op.getNumOperands! ctx = n ∧ op.getNumResults! ctx = 1 := by
  simp only [matchOp, bind, Option.bind, guard, pure, failure] at h
  grind

theorem matchOp_inBounds {op : OperationPtr} {ctx : IRContext OpCode} {n : Nat}
    {r : Array ValuePtr × propertiesOf (OpCode.felt Felt.add)}
    (h : matchOp op ctx (OpCode.felt Felt.add) n = some r) : op.InBounds ctx := by
  have hspec := (matchOp_spec h).1
  refine Decidable.byContradiction (fun hb => ?_)
  rw [OperationPtr.getOpType!, OperationPtr.get!_of_not_inBounds hb] at hspec
  exact absurd hspec (by decide)

namespace FeltPass

theorem matchAdd_inBounds {op : OperationPtr} {ctx : IRContext OpCode}
    {r : ValuePtr × ValuePtr × propertiesOf (OpCode.felt Felt.add)}
    (h : matchAdd op ctx = some r) : op.InBounds ctx := by
  unfold matchAdd at h
  simp only [bind, Option.bind] at h
  split at h <;> first | exact matchOp_inBounds (by assumption) | simp_all

/-- The `PatternRewriter.replaceValue` postcondition, exposed as a relation between the
    raw contexts via `Rewriter.replaceValue?`. -/
theorem replaceValue_post
    (rewriter rewriter' : PatternRewriter OpCode) (oldVal newVal : ValuePtr)
    (oldIn : oldVal.InBounds rewriter.ctx.raw) (newIn : newVal.InBounds rewriter.ctx.raw)
    (h : rewriter.replaceValue oldVal newVal oldIn newIn = some rewriter') :
    ∃ o n c d,
      Rewriter.replaceValue? rewriter.ctx.raw oldVal newVal o n c d = some rewriter'.ctx.raw := by
  -- `(addUsersInWorklist …)` only touches the worklist, leaving `.ctx = rewriter.ctx`; after
  -- unfolding, `simp_all` closes the goal using that equation together with the inner
  -- `replaceValue?` result equation.
  unfold PatternRewriter.replaceValue WfRewriter.replaceValue at h
  simp only [pure] at h
  split at h
  · simp at h
  · rename_i rawCtx hreplace
    split at hreplace
    · simp at hreplace
    · rename_i c hc
      have hctx := PatternRewriter.addUsersInWorklist_same_ctx (rewriter := rewriter)
        (value := oldVal) (hv := oldIn)
      refine ⟨oldIn, newIn, ?_, 1_000_000_000, ?_⟩
      · grind
      · -- `hc` gives the raw result `c`; tie it back to `rewriter'.ctx.raw`.
        simp only [Option.some.injEq] at h hreplace
        subst h
        simp only [← hreplace, ← hctx]
        exact hc

/-- `replaceValue` preserves an operation's region count. -/
theorem getNumRegions!_replaceValue
    (rewriter rewriter' : PatternRewriter OpCode) (oldVal newVal : ValuePtr) (op : OperationPtr)
    (oldIn : oldVal.InBounds rewriter.ctx.raw) (newIn : newVal.InBounds rewriter.ctx.raw)
    (h : rewriter.replaceValue oldVal newVal oldIn newIn = some rewriter') :
    op.getNumRegions! rewriter'.ctx.raw = op.getNumRegions! rewriter.ctx.raw := by
  obtain ⟨o, n, c, d, hrv⟩ := replaceValue_post rewriter rewriter' oldVal newVal oldIn newIn h
  exact OperationPtr.getNumRegions!_replaceValue? hrv

/-- `replaceValue` preserves `InBounds` of an operation. -/
theorem inBounds_replaceValue
    (rewriter rewriter' : PatternRewriter OpCode) (oldVal newVal : ValuePtr) (op : OperationPtr)
    (oldIn : oldVal.InBounds rewriter.ctx.raw) (newIn : newVal.InBounds rewriter.ctx.raw)
    (hOp : op.InBounds rewriter.ctx.raw)
    (h : rewriter.replaceValue oldVal newVal oldIn newIn = some rewriter') :
    op.InBounds rewriter'.ctx.raw := by
  obtain ⟨o, n, c, d, hrv⟩ := replaceValue_post rewriter rewriter' oldVal newVal oldIn newIn h
  have := Rewriter.replaceValue?_inBounds (GenericPtr.operation op) hrv
  grind

/-- `replaceValue` preserves an operation's result count. -/
theorem getNumResults!_replaceValue
    (rewriter rewriter' : PatternRewriter OpCode) (oldVal newVal : ValuePtr) (op : OperationPtr)
    (oldIn : oldVal.InBounds rewriter.ctx.raw) (newIn : newVal.InBounds rewriter.ctx.raw)
    (hOp : op.InBounds rewriter.ctx.raw)
    (h : rewriter.replaceValue oldVal newVal oldIn newIn = some rewriter') :
    op.getNumResults! rewriter'.ctx.raw = op.getNumResults! rewriter.ctx.raw := by
  obtain ⟨o, n, c, d, hrv⟩ := replaceValue_post rewriter rewriter' oldVal newVal oldIn newIn h
  exact Rewriter.replaceValue?_preserves_results_size op hOp hrv

/-- After `replaceValue oldVal newVal` (with `oldVal ≠ newVal`), `oldVal` has no uses. -/
theorem hasUses!_oldVal_replaceValue
    (rewriter rewriter' : PatternRewriter OpCode) (oldVal newVal : ValuePtr)
    (oldIn : oldVal.InBounds rewriter.ctx.raw) (newIn : newVal.InBounds rewriter.ctx.raw)
    (hNe : oldVal ≠ newVal)
    (h : rewriter.replaceValue oldVal newVal oldIn newIn = some rewriter') :
    oldVal.hasUses! rewriter'.ctx.raw = false := by
  obtain ⟨o, n, c, d, hrv⟩ := replaceValue_post rewriter rewriter' oldVal newVal oldIn newIn h
  exact ValuePtr.hasUses!_replaceValue_oldValue rewriter.ctx.wellFormed hNe hrv

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
    match hrep : rewriter.replaceValue (op.getResult 0) lhs hResIn hLhsIn with
    | none => none
    | some rewriter' =>
      -- Obligation #3: `replaceValue` preserves region count, reducing to the pre-state count
      -- (which the matcher does not constrain — see report).
      have hRegions : op.getNumRegions! rewriter'.ctx.raw = op.getNumRegions! rewriter.ctx.raw :=
        getNumRegions!_replaceValue rewriter rewriter' _ _ op hResIn hLhsIn hrep
      -- Obligation #5: `replaceValue` preserves `InBounds`.
      have hOpIn' : op.InBounds rewriter'.ctx.raw :=
        inBounds_replaceValue rewriter rewriter' _ _ op hResIn hLhsIn hIn hrep
      -- Obligation #4: after replacing all uses of `op.getResult 0` by `lhs`, the (sole)
      -- result has no uses, hence neither does `op`.
      have hNumRes' : op.getNumResults! rewriter'.ctx.raw = 1 := by
        rw [getNumResults!_replaceValue rewriter rewriter' _ _ op hResIn hLhsIn hIn hrep]
        exact hNumRes
      have hNoUses : op.hasUses! rewriter'.ctx.raw = false := by
        rw [OperationPtr.hasUses!_eq_false_iff_hasUses!_getResult_eq_false]
        intro i hi
        rw [hNumRes'] at hi
        obtain rfl : i = 0 := by omega
        exact hasUses!_oldVal_replaceValue rewriter rewriter' _ _ hResIn hLhsIn hNe hrep
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
    let sumVal := cstL.value.value + cstR.value.value
    let cstProp : FeltConstProperties :=
      { value := { value := sumVal, fieldType := cstL.value.fieldType } }
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

end FeltPass
end Veir
