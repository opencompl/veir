import Veir.Interpreter.EquationLemma
import Veir.Interpreter.Refinement.Basic
import Veir.Interpreter.Refinement.Lemmas
import Veir.Dominance

/-!
# Monotonicity of the interpreter

This file proves the monotonicity of `interpretOp`, `interpretOpList`, and
`interpretTerminatedOpList` under a cross-context interpreter state
refinement. This result is the key to prove the correctness of many transformations, as the
interpreter state refinement relation can be used to then prove the refinement of functions and
modules.

## Monotonicity of `interpretOp`
-/

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx ctx' : WfIRContext OpInfo}

/-- `VariableState.getOperandValues` is monotone with respect to the state refinement relation:
refined variable states produce refined operand arrays. -/
theorem VariableState.getOperandValues_isRefinedBy
    {srcVars : VariableState ctx} {tgtVars : VariableState ctx'} {mapping : ValueMapping ctx ctx'}
    (hRef : srcVars.isRefinedBy tgtVars mapping) (opIn : op.InBounds ctx.raw)
    (hOperands : op'.getOperands! ctx'.raw = mapping.applyToArray (op.getOperands! ctx.raw))
    (hSrc : srcVars.getOperandValues op = some srcVal) :
    ∃ tgtVal, tgtVars.getOperandValues op' = some tgtVal ∧ srcVal ⊒ tgtVal := by
  simp only [VariableState.isRefinedBy] at hRef
  have ⟨hsize, hSrc⟩ := VariableState.getOperandValues_eq_some_iff.mp hSrc
  have hSrc₂ := Array.mapM_option_isSome (f := tgtVars.getVar?) (l := op'.getOperands! ctx'.raw)
  have ⟨r, hr⟩ := hSrc₂ (by grind [ValueMapping.applyToArray])
  simp only [getOperandValues, hr, Option.some.injEq, exists_eq_left']
  simp only [RuntimeValue.arrayIsRefinedBy]
  constructor
  · grind
  · intro i hi
    grind [Array.mapM_option_eq_some_implies hr i (by grind), ValueMapping.applyToArray]

/-- `setResultValues?` preserves the state refinement. If the source/target variable states are
related by `mapping`, the freshly-computed result values refine (`resValues ⊒ resValues'`), `op`
and `op'` have the same results related by `mapping` (`hResults` and `hReflect`), then the target
`setResultValues?` also succeeds and the states after binding the results are again related by
`mapping`. -/
theorem VariableState.setResultValues?_isRefinedBy
    {srcVars : VariableState ctx} {tgtVars : VariableState ctx'}
    (hRef : srcVars.isRefinedBy tgtVars mapping) {newSrcVars : VariableState ctx}
    {srcVals tgtVals : Array RuntimeValue} (hVals : srcVals ⊒ tgtVals)
    (hResults : op'.getResults! ctx'.raw = mapping.applyToArray (op.getResults! ctx.raw))
    (hReflect : mapping.ReflectsResults op op')
    (hSrc : srcVars.setResultValues? op srcVals opIn = some newSrcVars)
    (tgtValsConforms : RuntimeValue.ArrayConforms tgtVals (op'.getResultTypes! ctx'.raw))
    (opIn' : op'.InBounds ctx'.raw) :
    ∃ newTgtVars, tgtVars.setResultValues? op' tgtVals opIn' = some newTgtVars ∧
                  newSrcVars.isRefinedBy newTgtVars mapping := by
  /- Conformance of the (refined) target values implies target success. -/
  have ⟨newTgtVars, hTgt⟩ :=
    (VariableState.setResultValues?_isSome_iff_conforms
      (varState := tgtVars) (inBounds := opIn')).mp tgtValsConforms
  simp only [hTgt, Option.some.injEq, exists_eq_left']
  /- Reason per element in the source and result value arrays. -/
  intro val valIn sv hsv
  /- Do a case analysis on whether or not the value is one of `op` results.
  If it is not, the value is not a result of `op'`, and the refinement follows from the
  original `VariableState` refinement.
  If it is, then because of `hReflect`, the value is mapped to a result of `op'`, and the
  refinement follows the `RuntimeValue` array refinement. -/
  cases OperationPtr.getResults!_not_mem_or_eq_getResult ctx.raw val op
  next hNotMem => grind [VariableState.isRefinedBy]
  next hMem =>
    have hfix := ValueMapping.applyToArray_getResults!_ext opIn hResults.symm
    grind [RuntimeValue.arrayIsRefinedBy]

/-- `setArgumentValues?` preserves the state refinement. If the source/target variable states are
related by `mapping`, the block argument values refine pointwise (`values ⊒ values'`), the
renaming `mapping` doesn't change the block arguments (`hArgs` and `hReflectArgs`), and the target
values conform to the target argument types (`tgtConforms`), then the target `setArgumentValues?`
also succeeds and the states after binding the block arguments are again related by `mapping`. -/
theorem VariableState.setArgumentValues?_isRefinedBy {ctx ctx' : WfIRContext OpCode}
    {srcVars : VariableState ctx} {tgtVars : VariableState ctx'} {mapping : ValueMapping ctx ctx'}
    {block : BlockPtr} {values values' : Array RuntimeValue} {newSrcVars : VariableState ctx}
    (hRef : srcVars.isRefinedBy tgtVars mapping)
    (hVals : values ⊒ values')
    (blockIn : block.InBounds ctx.raw) (blockIn' : block.InBounds ctx'.raw)
    (hArgs : block.getArguments! ctx'.raw = mapping.applyToArray (block.getArguments! ctx.raw))
    (hReflectArgs : ∀ (val : ValuePtr) (valIn : val.InBounds ctx.raw) (arg : ValuePtr),
        arg ∈ block.getArguments! ctx'.raw →
        (mapping ⟨val, valIn⟩).val = arg → val = arg)
    (tgtConforms : ∀ j, j < block.getNumArguments! ctx'.raw →
        (values'[j]!).Conforms ((block.getArguments! ctx'.raw)[j]!.getType! ctx'.raw))
    (hSrc : srcVars.setArgumentValues? block values blockIn = some newSrcVars) :
    ∃ newTgtVars, tgtVars.setArgumentValues? block values' blockIn' = some newTgtVars ∧
                  newSrcVars.isRefinedBy newTgtVars mapping := by
  -- `applyToArray` preserves size, so the two blocks have the same number of arguments; the renaming
  -- fixes every block argument (`hArgs` is the pointwise "fixes" equation in array form).
  have hNumArgs : block.getNumArguments! ctx'.raw = block.getNumArguments! ctx.raw := by
    have := congrArg Array.size hArgs
    simpa using this
  have hFix : ∀ (val : ValuePtr) (valIn : val.InBounds ctx.raw),
      val ∈ block.getArguments! ctx.raw → (mapping ⟨val, valIn⟩).val = val := by
    intro val valIn hMem
    obtain ⟨i, hi, rfl⟩ := BlockPtr.getArguments!.mem_iff_exists_index.mp hMem
    exact ValueMapping.applyToArray_getArguments!_ext blockIn hArgs.symm i hi
  -- Target success follows from conformance of the (refined) target values.
  have tgtConforms' : ∀ j, j < block.getNumArguments! ctx'.raw →
      (values'[j]!).Conforms ((block.getArgument j : ValuePtr).getType! ctx'.raw) := by
    intro j hj
    rw [← BlockPtr.getArguments!.getElem!_eq_getArgument hj]
    exact tgtConforms j hj
  have ⟨newTgtVars, hTgt⟩ :=
    (VariableState.setArgumentValues?_isSome_iff_conforms tgtVars
      (block := block) (blockInBounds := blockIn')).mp tgtConforms'
  refine ⟨newTgtVars, hTgt, ?_⟩
  -- Pointwise refinement of the value arrays at every argument index. Out-of-range indices read the
  -- same `default` on both sides (the arrays have equal size by `hVals`), so refinement holds there too.
  have hPt : ∀ i, i < block.getNumArguments! ctx.raw → values[i]! ⊒ values'[i]! := by
    intro i _hi
    obtain ⟨hsize, hpt⟩ := hVals
    by_cases h : i < values.size
    · exact hpt i h
    · rw [getElem!_neg values i h, getElem!_neg values' i (hsize ▸ h)]
      exact RuntimeValue.isRefinedBy_refl _
  intro val valIn sv hsv
  by_cases hMem : val ∈ block.getArguments! ctx.raw
  · -- `val` is a block argument `block.getArgument i`, set to `values[i]!`/`values'[i]!`.
    obtain ⟨i, hi, rfl⟩ := BlockPtr.getArguments!.mem_iff_exists_index.mp hMem
    have hsrcval := VariableState.getVar?_getArgument_of_setArgumentValues? hi hSrc
    rw [hsv] at hsrcval
    obtain rfl : sv = values[i]! := (Option.some.injEq ..).mp hsrcval
    refine ⟨values'[i]!, ?_, hPt i hi⟩
    rw [hFix (block.getArgument i) valIn hMem]
    exact VariableState.getVar?_getArgument_of_setArgumentValues? (hNumArgs ▸ hi) hTgt
  · -- `val` is not a block argument: its value is unchanged on both sides; use `hRef`.
    rw [VariableState.getVar?_setArgumentValues?_of_notMem_getArguments! hMem hSrc] at hsv
    obtain ⟨tv, htv, href⟩ := hRef val valIn sv hsv
    refine ⟨tv, ?_, href⟩
    -- `mapping val` is not a block argument either (else `hReflectArgs` forces `val` to be one).
    have hσnotMem : (mapping ⟨val, valIn⟩).val ∉ block.getArguments! ctx'.raw := by
      intro hm
      obtain ⟨i, hi, heq⟩ := BlockPtr.getArguments!.mem_iff_exists_index.mp hm
      have harg : (block.getArgument i : ValuePtr) ∈ block.getArguments! ctx'.raw :=
        BlockPtr.getArguments!.mem_iff_exists_index.mpr ⟨i, hi, rfl⟩
      exact hMem (BlockPtr.getArguments!.mem_iff_exists_index.mpr
        ⟨i, hNumArgs ▸ hi, (hReflectArgs val valIn _ harg heq.symm).symm⟩)
    rw [VariableState.getVar?_setArgumentValues?_of_notMem_getArguments! hσnotMem hTgt]
    exact htv

/-- `setArgumentValues?` preserves the *scoped* state refinement `isRefinedByAt`.

Hypotheses compared to `setArgumentValues?_isRefinedBy`:
- `hRef` uses `isRefinedByAt` at `(p, p')` instead of unscoped `isRefinedBy`
- `hImageNotArg`: the mapping does not send a non-argument value that is *in scope at the block
  entry* onto a block-argument slot. (Justified by dominance: a forwarded block argument dominates
  the value it replaces, so it cannot also be dominated by it — hence no value dominating the block
  entry maps onto one of the block's own arguments.)
- `ctxDom`/`ctxDom'`: the source/target contexts satisfy SSA dominance, which lets us conclude that
  a non-argument value dominating the block entry already dominates the predecessor's end (via
  `WfIRContext.Dom.value_dominatesIp_successor_entry`). -/
theorem VariableState.setArgumentValues?_isRefinedByAt {ctx ctx' : WfIRContext OpCode}
    {srcVars : VariableState ctx} {tgtVars : VariableState ctx'}
    {mapping : ValueMapping ctx ctx'}
    {values values' : Array RuntimeValue} {newSrcVars : VariableState ctx}
    (predInBounds : pred.InBounds ctx.raw) (predInBounds' : pred.InBounds ctx'.raw)
    (ctxDom : ctx.Dom) (ctxDom' : ctx'.Dom)
    (hRef : srcVars.isRefinedByAt tgtVars mapping (InsertPoint.atEnd pred) (InsertPoint.atEnd pred))
    (hVals : values ⊒ values')
    (blockIn : block.InBounds ctx.raw) (blockIn' : block.InBounds ctx'.raw)
    (blockIsSucc : block ∈ pred.getSuccessors! ctx.raw)
    (blockIsSucc' : block ∈ pred.getSuccessors! ctx'.raw)
    (hArgs : block.getArguments! ctx'.raw = mapping.applyToArray (block.getArguments! ctx.raw))
    /- A non-argument value that is in scope at the block entry is never mapped onto a block-argument
       slot. Dischargeable from dominance: a forwarded block argument dominates the value it replaces,
       so a value dominating the block entry cannot map onto one of that block's arguments. -/
    (hImageNotArg : ∀ (val : ValuePtr) (valIn : val.InBounds ctx.raw),
        val ∉ block.getArguments! ctx.raw →
        val.dominatesIp (InsertPoint.atStart! block ctx.raw) ctx →
        (mapping ⟨val, valIn⟩).val ∉ block.getArguments! ctx'.raw)
    (tgtConforms : ∀ j, j < block.getNumArguments! ctx'.raw →
        (values'[j]!).Conforms ((block.getArguments! ctx'.raw)[j]!.getType! ctx'.raw))
    (hSrc : srcVars.setArgumentValues? block values blockIn = some newSrcVars) :
    ∃ newTgtVars, tgtVars.setArgumentValues? block values' blockIn' = some newTgtVars ∧
      newSrcVars.isRefinedByAt newTgtVars mapping
        (InsertPoint.atStart! block ctx.raw) (InsertPoint.atStart! block ctx'.raw) := by
  have hNumArgs : block.getNumArguments! ctx'.raw = block.getNumArguments! ctx.raw := by
    have := congrArg Array.size hArgs; simpa using this
  have tgtConforms' : ∀ j, j < block.getNumArguments! ctx'.raw →
      (values'[j]!).Conforms ((block.getArgument j : ValuePtr).getType! ctx'.raw) := by
    intro j hj
    rw [← BlockPtr.getArguments!.getElem!_eq_getArgument hj]
    exact tgtConforms j hj
  have ⟨newTgtVars, hTgt⟩ :=
    (VariableState.setArgumentValues?_isSome_iff_conforms tgtVars
      (block := block) (blockInBounds := blockIn')).mp tgtConforms'
  refine ⟨newTgtVars, hTgt, ?_⟩
  -- Pointwise refinement between source/target argument values.
  have hPt : ∀ i, i < block.getNumArguments! ctx.raw → values[i]! ⊒ values'[i]! := by
    intro i _hi
    obtain ⟨hsize, hpt⟩ := hVals
    by_cases h : i < values.size
    · exact hpt i h
    · rw [getElem!_neg values i h, getElem!_neg values' i (hsize ▸ h)]
      exact RuntimeValue.isRefinedBy_refl _
  -- Prove `isRefinedByAt` at `(atStart! block ctx.raw, atStart! block ctx'.raw)`.
  intro val valIn hValDom hσValDom sv tv hsv htv
  by_cases hMem : val ∈ block.getArguments! ctx.raw
  · -- `val` is a block argument: it was just set to `values[i]!`; target gets `values'[i]!`.
    obtain ⟨i, hi, rfl⟩ := BlockPtr.getArguments!.mem_iff_exists_index.mp hMem
    have hsrcval := VariableState.getVar?_getArgument_of_setArgumentValues? hi hSrc
    rw [hsv] at hsrcval; obtain rfl : sv = values[i]! := (Option.some.injEq ..).mp hsrcval
    have hfixI : (mapping ⟨block.getArgument i, by grind⟩).val = block.getArgument i :=
      ValueMapping.applyToArray_getArguments!_ext blockIn hArgs.symm i hi
    rw [hfixI] at htv
    have htv' := VariableState.getVar?_getArgument_of_setArgumentValues? (hNumArgs ▸ hi) hTgt
    rw [htv] at htv'; obtain rfl : tv = values'[i]! := (Option.some.injEq ..).mp htv'
    exact hPt i hi
  · rw [VariableState.getVar?_setArgumentValues?_of_notMem_getArguments! hMem hSrc] at hsv
    -- `mapping val` is not a block argument either: `val` is in scope at the block entry, so by
    -- `hImageNotArg` its image cannot land on one of the block's arguments.
    have hσnotMem : (mapping ⟨val, valIn⟩).val ∉ block.getArguments! ctx'.raw :=
      hImageNotArg val valIn hMem hValDom
    rw [VariableState.getVar?_setArgumentValues?_of_notMem_getArguments! hσnotMem hTgt] at htv
    -- A non-argument value dominating the block entry already dominates the predecessor's end,
    -- by `value_dominatesIp_successor_entry` (the value is not a block argument, so the
    -- "is an argument" disjunct is excluded).
    have hValDomPred : val.dominatesIp (InsertPoint.atEnd pred) ctx :=
      (WfIRContext.Dom.value_dominatesIp_successor_entry ctxDom predInBounds blockIsSucc
        hValDom).resolve_right hMem
    have hσValDomPred : (mapping ⟨val, valIn⟩).val.dominatesIp (InsertPoint.atEnd pred) ctx' :=
      (WfIRContext.Dom.value_dominatesIp_successor_entry ctxDom' predInBounds' blockIsSucc'
        hσValDom).resolve_right hσnotMem
    exact hRef val valIn hValDomPred hσValDomPred sv tv hsv htv

/-! ## Scoped (`isRefinedByAt`) variants of the monotonicity lemmas -/

/-- `getOperandValues` is monotone under scoped state refinement. The target operand values
exist by `DefinesDominating`; operand dominance comes from `ctx.Dom` and `ctx'.Dom`. -/
theorem VariableState.getOperandValues_isRefinedByAt
    {ctx ctx' : WfIRContext OpCode}
    {srcVars : VariableState ctx} {tgtVars : VariableState ctx'}
    {mapping : ValueMapping ctx ctx'}
    (opIn : op.InBounds ctx.raw) (opIn' : op'.InBounds ctx'.raw)
    (hRef : srcVars.isRefinedByAt tgtVars mapping (.before op) (.before op'))
    (ctxDom : ctx.Dom)
    (ctxDom' : ctx'.Dom)
    (hOperands : op'.getOperands! ctx'.raw = mapping.applyToArray (op.getOperands! ctx.raw))
    (tgtDef : ∀ (v : ValuePtr) (_vIn : v.InBounds ctx'.raw),
         v.dominatesIp (.before op') ctx' → (tgtVars.getVar? v).isSome)
    (hSrc : srcVars.getOperandValues op = some srcVal) :
    ∃ tgtVal, tgtVars.getOperandValues op' = some tgtVal ∧ srcVal ⊒ tgtVal := by
  simp only [VariableState.isRefinedByAt] at hRef
  have ⟨hsize, hSrc'⟩ := VariableState.getOperandValues_eq_some_iff.mp hSrc
  -- All target operands are defined (from `tgtDef` + target operand dominance via `ctxDom'`).
  have hTgtDef : ∀ (i : Nat) (hi : i < (op'.getOperands! ctx'.raw).size),
      (tgtVars.getVar? (op'.getOperands! ctx'.raw)[i]).isSome := by
    intro i hi
    have hmem : (op'.getOperands! ctx'.raw)[i] ∈ op'.getOperands! ctx'.raw :=
      Array.getElem_mem hi
    have hdom : ((op'.getOperands! ctx'.raw)[i]).dominatesIp (.before op') ctx' :=
      ctxDom'.operand_dominates_op opIn' hmem
    exact tgtDef _ (by grind) hdom
  -- Hence the target operand array is fully defined, so `getOperandValues op'` succeeds.
  obtain ⟨tgtVal, hTgt⟩ := Array.mapM_option_isSome (f := tgtVars.getVar?)
    (l := op'.getOperands! ctx'.raw) hTgtDef
  have hTgtEq : tgtVars.getOperandValues op' = some tgtVal := by
    simpa [VariableState.getOperandValues] using hTgt
  refine ⟨tgtVal, hTgtEq, ?_⟩
  -- Pointwise: each source operand value refines its target counterpart.
  obtain ⟨htsize, hTgt'⟩ := VariableState.getOperandValues_eq_some_iff.mp hTgtEq
  -- The `i`-th operand of `op'` is the image under `mapping` of the `i`-th operand of `op`.
  have hOpEq : ∀ (i : Nat) (hi : i < op.getNumOperands! ctx.raw),
      op'.getOperand! ctx'.raw i = (mapping ⟨op.getOperand! ctx.raw i, by grind⟩).val := by
    intro i hi
    simp only [ValueMapping.applyToArray, Array.ext_iff, Array.size_map, Array.size_attach,
      OperationPtr.getOperands!.size_eq_getNumOperands!, Array.getElem_map,
      Array.getElem_attach] at hOperands
    obtain ⟨_, hpt⟩ := hOperands
    have := hpt i (by grind) (by grind)
    grind [OperationPtr.getOperands!, OperationPtr.getOperand!, OperationPtr.getNumOperands!]
  refine ⟨by grind, ?_⟩
  intro i hi
  have hi' : i < op.getNumOperands! ctx.raw := by grind
  -- The `i`-th source operand, in scope at `.before op`.
  have valIn : (op.getOperand! ctx.raw i).InBounds ctx.raw := by grind
  have hmem : (op.getOperand! ctx.raw i) ∈ op.getOperands! ctx.raw :=
    OperationPtr.getOperands!.mem_getOperand hi'
  have hsdom : (op.getOperand! ctx.raw i).dominatesIp (.before op) ctx :=
    ctxDom.operand_dominates_op opIn hmem
  -- Its image is the `i`-th target operand, in scope at `.before op'`.
  have hσmem : (mapping ⟨op.getOperand! ctx.raw i, valIn⟩).val ∈ op'.getOperands! ctx'.raw := by
    rw [← hOpEq i hi']
    exact OperationPtr.getOperands!.mem_getOperand (by grind)
  have hσdom : (mapping ⟨op.getOperand! ctx.raw i, valIn⟩).val.dominatesIp (.before op') ctx' :=
    ctxDom'.operand_dominates_op opIn' hσmem
  have htv : tgtVars.getVar? (mapping ⟨op.getOperand! ctx.raw i, valIn⟩) = some tgtVal[i]! := by
    rw [← hOpEq i hi']
    exact hTgt' i (by grind)
  exact hRef (op.getOperand! ctx.raw i) valIn hsdom hσdom _ _ (hSrc' i hi') htv

/-- `setResultValues?` preserves the scoped state refinement, advancing the scope from
`(before op, before op')` to `(after op, after op')`. Newly-in-scope results are refined
by `hVals`; pre-existing values carry through via `value_dominatesIp_after_iff`. -/
theorem VariableState.setResultValues?_isRefinedByAt
    {ctx ctx' : WfIRContext OpCode}
    {srcVars : VariableState ctx} {tgtVars : VariableState ctx'}
    {mapping : ValueMapping ctx ctx'}
    (opIn : op.InBounds ctx.raw) (opIn' : op'.InBounds ctx'.raw)
    (hRef : srcVars.isRefinedByAt tgtVars mapping (.before op) (.before op'))
    {newSrcVars : VariableState ctx}
    {srcVals tgtVals : Array RuntimeValue} (hVals : srcVals ⊒ tgtVals)
    (hResults : op'.getResults! ctx'.raw = mapping.applyToArray (op.getResults! ctx.raw))
    (hReflect : mapping.ReflectsResults op op')
    (hSrc : srcVars.setResultValues? op srcVals opIn = some newSrcVars)
    (tgtValsConforms : RuntimeValue.ArrayConforms tgtVals (op'.getResultTypes! ctx'.raw))
    (ctxDom : ctx.Dom) (ctxDom' : ctx'.Dom)
    (opHasParent : (op.get! ctx.raw).parent = some block)
    (opHasParent' : (op'.get! ctx'.raw).parent = some block') :
    ∃ newTgtVars, tgtVars.setResultValues? op' tgtVals opIn' = some newTgtVars ∧
      newSrcVars.isRefinedByAt newTgtVars mapping
        (InsertPoint.after op ctx.raw block opHasParent opIn)
        (InsertPoint.after op' ctx'.raw block' opHasParent' opIn') := by
  have ⟨newTgtVars, hTgt⟩ :=
    (VariableState.setResultValues?_isSome_iff_conforms
      (varState := tgtVars) (inBounds := opIn')).mp tgtValsConforms
  refine ⟨newTgtVars, hTgt, ?_⟩
  intro val valIn hValDomAfter hσValDomAfter sv tv hsv htv
  -- By `value_dominatesIp_after_iff`: val dominates (before op) or is a result of op.
  rw [ctxDom.value_dominatesIp_after_iff] at hValDomAfter
  rw [ctxDom'.value_dominatesIp_after_iff] at hσValDomAfter
  cases OperationPtr.getResults!_not_mem_or_eq_getResult ctx.raw val op with
  | inl hNotMem =>
    -- `val` is not a result of `op`: unchanged by `setResultValues?` on both sides.
    rw [VariableState.getVar?_setResultValues?_of_notMem_getResults! hNotMem hSrc] at hsv
    have hσNotMem := (hReflect.not_mem_getResults valIn hNotMem)
    rw [VariableState.getVar?_setResultValues?_of_notMem_getResults! hσNotMem hTgt] at htv
    have hValDomBefore : val.dominatesIp (.before op) ctx :=
      hValDomAfter.resolve_right hNotMem
    have hσValDomBefore : (mapping ⟨val, valIn⟩).val.dominatesIp (.before op') ctx' :=
      hσValDomAfter.resolve_right hσNotMem
    exact hRef val valIn hValDomBefore hσValDomBefore sv tv hsv htv
  | inr hMem =>
    -- `val` is a result of `op`: newly set by `setResultValues?`, refined by `hVals`.
    have hfix := ValueMapping.applyToArray_getResults!_ext opIn hResults.symm
    grind [RuntimeValue.arrayIsRefinedBy]

/-- `interpretOp` is monotone under a *cross-context* scoped interpreter-state refinement.
The source/target points are `(.before op, .before op')` at entry and advance to
`(.after op, .after op')` at exit. -/
theorem interpretOp_monotone_at
    {ctx ctx' : WfIRContext OpCode}
    {state : InterpreterState ctx} {state' : InterpreterState ctx'}
    {mapping : ValueMapping ctx ctx'}
    (opIn : op.InBounds ctx.raw) (opIn' : op'.InBounds ctx'.raw)
    (hState : state.isRefinedByAt state' mapping (.before op) (.before op'))
    (hPreserves : mapping.PreservesOperation op op')
    (opVerif' : op'.Verified ctx' opIn')
    (ctxDom : ctx.Dom) (ctxDom' : ctx'.Dom)
    (tgtDefDom : state'.DefinesDominating (.before op') opIn')
    (opHasParent : (op.get! ctx.raw).parent = some block)
    (opHasParent' : (op'.get! ctx'.raw).parent = some block') :
    Interp.isRefinedBy
      (fun (r₁ : InterpreterState ctx × Option ControlFlowAction)
           (r₂ : InterpreterState ctx' × Option ControlFlowAction) =>
        r₁.1.isRefinedByAt r₂.1 mapping
          (InsertPoint.after op ctx.raw block opHasParent opIn)
          (InsertPoint.after op' ctx'.raw block' opHasParent' opIn') ∧
        ControlFlowAction.optionIsRefinedBy r₁.2 r₂.2)
      (interpretOp op state opIn)
      (interpretOp op' state' opIn') := by
  -- If the source interpretation fails, then the refinement is trivial.
  by_cases hsource : interpretOp op state opIn = none; simp [hsource, Interp.isRefinedBy]
  -- Source/target operands are defined and refined (target existence via `tgtDefDom`).
  have ⟨operands, hSrcOps⟩ : ∃ operands, state.variables.getOperandValues op = some operands := by
    grind [interpretOp]
  obtain ⟨operands', hTgtOps, hOpsRef⟩ :=
    VariableState.getOperandValues_isRefinedByAt opIn opIn' hState.2 ctxDom ctxDom'
      hPreserves.operands tgtDefDom hSrcOps
  have hMem : state.memory = state'.memory := hState.1
  -- Refinement of the pure `interpretOp'` on the refined operand arrays.
  have hPR1 := interpretOp'_monotone (op.getOpType! ctx.raw)
    (op.getProperties! ctx.raw (op.getOpType! ctx.raw)) (op.getResultTypes! ctx.raw)
    operands operands' (op.getSuccessors! ctx.raw) state.memory hOpsRef
  have hInterp'Eq : op'.interpret ctx'.raw operands' state'.memory =
                    op.interpret ctx.raw operands' state.memory := by
     grind [interpretOp'_opType_cast, cases ValueMapping.PreservesOperation]
  rcases hsrc : interpretOp op state opIn with _ | (⟨state₂, act⟩ | _)
  · simp [Interp.isRefinedBy]
  · simp only [Interp.isRefinedBy_ok_target_iff, Prod.exists]
    have ⟨resValues, hinterp', hResValues⟩ :=
      (interpretOp_ok_iff_of_getOperandValues_eq_some hSrcOps).mp hsrc
    simp only [hinterp', Interp.isRefinedBy_ok_target_iff, Prod.exists] at hPR1
    have ⟨resValues', memory'₂, act', hinterp'Tgt, resValuesRef, memoryEq, actRef⟩ := hPR1
    subst memory'₂
    simp only [← hInterp'Eq] at hinterp'Tgt
    simp only [interpretOp, hTgtOps, bind, hinterp'Tgt, liftM, monadLift, MonadLift.monadLift]
    have tgtConf := interpretOp'_results_conform (opInBounds := opIn') opVerif'
      (VariableState.getOperandValues_conforms hTgtOps) hinterp'Tgt
    -- Bind the results on both sides; the scoped relation advances to `(after op, after op')`.
    obtain ⟨newTgtVars, hSetTgt, hRefAt⟩ :=
      VariableState.setResultValues?_isRefinedByAt opIn opIn' hState.2 resValuesRef
        hPreserves.results hPreserves.reflect hResValues tgtConf ctxDom ctxDom'
        opHasParent opHasParent'
    simp only [Interp, hSetTgt, pure, Option.some.injEq, UBOr.ok.injEq, Prod.mk.injEq]
    grind [InterpreterState.isRefinedByAt]
  · simp

/-- `interpretOpList` is monotone under scoped state refinement, over an *identical* op list that
forms an operation chain slice of `block`/`block'` in both contexts. The scoped invariant is carried
through each step by `interpretOp_monotone_at`, the target `DefinesDominating` invariant by
`interpretOp_DefinesDominating`, and the scope point advanced across each op via the chain
`.next`-link. The end point is `InsertPoint.afterLast ops _ p`: the point after the last operation
(or the start point `p`/`p'` if the list is empty). Only the **last** operation may produce a
control-flow action (`hOnlyLastAction`), so an early stop cannot leave the result state at a scope
point past where interpretation actually halted. -/
theorem interpretOpList_monoAt
    {ctx ctx' : WfIRContext OpCode} (hVerif : ctx'.Verified)
    (ctxDom : ctx.Dom) (ctxDom' : ctx'.Dom)
    {block block' : BlockPtr} {ops : List OperationPtr}
    (opsInBounds : ∀ op, op ∈ ops → op.InBounds ctx.raw)
    (opsInBounds' : ∀ op, op ∈ ops → op.InBounds ctx'.raw)
    (hChain : block.OpChainSlice ctx.raw ops)
    (hChain' : block'.OpChainSlice ctx'.raw ops)
    {mapping : ValueMapping ctx ctx'}
    {state : InterpreterState ctx} {state' : InterpreterState ctx'}
    {p p' : InsertPoint}
    (pIn : p.InBounds ctx.raw) (p'In : p'.InBounds ctx'.raw)
    (hState : state.isRefinedByAt state' mapping p p')
    (tgtDefDom : state'.DefinesDominating p' p'In)
    (hPreserves : ∀ op, (h : op ∈ ops) → mapping.PreservesOperation op op)
    (hPointsHead : ∀ (h : ops ≠ []), p = .before (ops.head h) ∧ p' = .before (ops.head h))
    (hOnlyLastAction : ∀ op, op ∈ ops.dropLast →
        ∀ (st : InterpreterState ctx) (stIn : op.InBounds ctx.raw)
          (st' : InterpreterState ctx) (cf : ControlFlowAction),
          interpretOp op st stIn ≠ some (.ok (st', some cf))) :
    Interp.isRefinedBy
      (fun (r₁ : InterpreterState ctx × Option ControlFlowAction)
           (r₂ : InterpreterState ctx' × Option ControlFlowAction) =>
        r₁.1.isRefinedByAt r₂.1 mapping
          (InsertPoint.afterLast ops ctx.raw p) (InsertPoint.afterLast ops ctx'.raw p') ∧
        ControlFlowAction.optionIsRefinedBy r₁.2 r₂.2)
      (interpretOpList ops state opsInBounds)
      (interpretOpList ops state' opsInBounds') := by
  induction ops generalizing state state' p p' with
  | nil =>
    simp only [interpretOpList_nil, InsertPoint.afterLast_nil, Interp.isRefinedBy_ok_target_iff]
    exact ⟨_, rfl, hState, by simp [ControlFlowAction.optionIsRefinedBy]⟩
  | cons a l ih =>
    rw [BlockPtr.OpChainSlice.cons_iff] at hChain hChain'
    obtain ⟨aIn, aParent, aNext, hChainL⟩ := hChain
    obtain ⟨aIn', aParent', aNext', hChainL'⟩ := hChain'
    obtain ⟨hpa, hpa'⟩ := hPointsHead (by simp)
    simp only [List.head_cons] at hpa hpa'
    subst hpa hpa'
    -- Advance the end point past the head: `afterLast (a :: l)` from `.before a` is
    -- `afterLast l` from `after a`, matching how the recursion advances the start point.
    simp only [InsertPoint.afterLast_cons_after l (.before a) aParent aIn,
      InsertPoint.afterLast_cons_after l (.before a) aParent' aIn']
    have refinesHead := interpretOp_monotone_at aIn aIn' hState
      (hPreserves a (by simp)) (by grind) ctxDom ctxDom' tgtDefDom aParent aParent'
    simp only [interpretOpList_cons]
    rcases hsrc : interpretOp a state aIn with _ | (⟨s, act⟩ | _)
    · simp [Interp.isRefinedBy]
    · simp only [hsrc, Interp.isRefinedBy_ok_target_iff] at refinesHead
      obtain ⟨⟨s', act'⟩, htgt, hsRef, hactRef⟩ := refinesHead
      simp only [htgt]
      cases act with
      | none =>
        have hact' : act' = none := by grind [ControlFlowAction.optionIsRefinedBy]
        subst hact'
        simp only
        have tgtDomAfter : s'.DefinesDominating (InsertPoint.after a ctx'.raw block') :=
          interpretOp_DefinesDominating ctxDom' tgtDefDom aParent' htgt
        have hdropSub : ∀ op, op ∈ l.dropLast → op ∈ (a :: l).dropLast := by
          intro op hop
          cases l with
          | nil => simp at hop
          | cons b rest => simp_all [List.dropLast]
        refine ih (hChain := hChainL) (hChain' := hChainL')
          (p := InsertPoint.after a ctx.raw block aParent aIn)
          (p' := InsertPoint.after a ctx'.raw block' aParent' aIn')
          (pIn := by grind) (p'In := by grind) (hState := hsRef) (tgtDefDom := tgtDomAfter)
          (hPreserves := fun op hop => hPreserves op (List.mem_cons_of_mem a hop))
          (hPointsHead := ?_)
          (hOnlyLastAction := fun op hop => hOnlyLastAction op (hdropSub op hop))
        · intro hl
          have hb : l.head? = some (l.head hl) := by
            cases l with
            | nil => exact absurd rfl hl
            | cons b rest => rfl
          exact ⟨InsertPoint.after_eq_of_some_next (aNext _ hb),
                 InsertPoint.after_eq_of_some_next (aNext' _ hb)⟩
      | some cf =>
        obtain rfl : l = [] := by
          rcases l with _ | ⟨b, rest⟩
          · rfl
          · exact absurd hsrc (hOnlyLastAction a (by simp [List.dropLast]) state aIn s cf)
        -- `afterLast [] _ (after a ..)` is just `after a ..`, where `hsRef` already lands.
        have ⟨cf', hact', hcfRef⟩ : ∃ cf', act' = some cf' ∧ cf.isRefinedBy cf' := by
          cases act' <;> simp_all [ControlFlowAction.optionIsRefinedBy]
        subst hact'
        simp [Interp, hsRef, InsertPoint.afterLast_nil, ControlFlowAction.optionIsRefinedBy, hcfRef]
    · simp

/-- `interpretTerminatedOpList` is monotone under scoped state refinement. Wraps
`interpretOpList_monoAt`; the terminator is the last operation, so its action coincides with the end
point `InsertPoint.afterLast ops _ p`. -/
theorem interpretTerminatedOpList_monoAt
    {ctx ctx' : WfIRContext OpCode} (ctx'Verif : ctx'.Verified)
    (ctxDom : ctx.Dom) (ctxDom' : ctx'.Dom)
    {block block' : BlockPtr} {ops : List OperationPtr}
    (opsInBounds : ∀ op, op ∈ ops → op.InBounds ctx.raw)
    (opsInBounds' : ∀ op, op ∈ ops → op.InBounds ctx'.raw)
    (hChain : block.OpChainSlice ctx.raw ops)
    (hChain' : block'.OpChainSlice ctx'.raw ops)
    {state : InterpreterState ctx} {state' : InterpreterState ctx'}
    {mapping : ValueMapping ctx ctx'} {p p' : InsertPoint}
    (pIn : p.InBounds ctx.raw) (p'In : p'.InBounds ctx'.raw)
    (hState : state.isRefinedByAt state' mapping p p')
    (tgtDefDom : state'.DefinesDominating p' p'In)
    (hFrame : ∀ op, (h : op ∈ ops) → mapping.PreservesOperation op op)
    (hPointsHead : ∀ (h : ops ≠ []), p = .before (ops.head h) ∧ p' = .before (ops.head h))
    (hOnlyLastAction : ∀ op, op ∈ ops.dropLast →
        ∀ (st : InterpreterState ctx) (stIn : op.InBounds ctx.raw)
          (st' : InterpreterState ctx) (cf : ControlFlowAction),
          interpretOp op st stIn ≠ some (.ok (st', some cf))) :
    Interp.isRefinedBy
      (fun (r₁ : InterpreterState ctx × ControlFlowAction)
           (r₂ : InterpreterState ctx' × ControlFlowAction) =>
        r₁.1.isRefinedByAt r₂.1 mapping
          (InsertPoint.afterLast ops ctx.raw p) (InsertPoint.afterLast ops ctx'.raw p') ∧
        r₁.2.isRefinedBy r₂.2)
      (interpretTerminatedOpList ops state opsInBounds)
      (interpretTerminatedOpList ops state' opsInBounds') := by
  have hList := interpretOpList_monoAt ctx'Verif ctxDom ctxDom' opsInBounds opsInBounds'
    hChain hChain' pIn p'In hState tgtDefDom hFrame hPointsHead hOnlyLastAction
  simp only [interpretTerminatedOpList, bind]
  rcases hsrc : interpretOpList ops state opsInBounds with _ | (⟨s, act⟩ | _)
  · simp [Interp.isRefinedBy]
  · simp only [hsrc, Interp.isRefinedBy_ok_target_iff] at hList
    obtain ⟨⟨s', act'⟩, htgt, hsRef, hactRef⟩ := hList
    simp only [htgt]
    cases act with
    | none => simp [Interp.isRefinedBy]
    | some cf =>
      have ⟨cf', hact', hcfRef⟩ : ∃ cf', act' = some cf' ∧ cf.isRefinedBy cf' := by
        cases act' <;> simp_all [ControlFlowAction.optionIsRefinedBy]
      subst hact'
      exact ⟨hsRef, hcfRef⟩
  · exact Interp.isRefinedBy_ub_target

/--
`interpretOp` is monotone under a *cross-context* interpreter-state refinement.

Lift `interpretOp'_monotone` through `getOperandValues` and `setResultValues?`. The source state
lives in `ctx`, the target in `ctx'`, related by `InterpreterState.isRefinedBy` through the value
renaming `mapping` (for the unchanged majority, `mapping` is the identity-on-`ValuePtr` `InBounds`-embedding).

The conclusion relates the two `interpretOp` results: their interpreter states are again related by
`InterpreterState.isRefinedBy mapping`, and their control flow actions by `ControlFlowAction`-refinement.
Because the state relation constrains only values defined in *both* states, `op`'s freshly-set
results are added on both sides and re-established by `interpretOp'_monotone`, while pre-existing
values stay defined and refined.
-/
theorem interpretOp_monotone
    {ctx ctx' : WfIRContext OpCode}
    {state : InterpreterState ctx} {state' : InterpreterState ctx'}
    {mapping : ValueMapping ctx ctx'}
    (opIn : op.InBounds ctx.raw) (opIn' : op'.InBounds ctx'.raw)
    (hState : state.isRefinedBy state' mapping)
    (hPreserves : mapping.PreservesOperation op op')
    (opVerif' : op'.Verified ctx' opIn') :
    Interp.isRefinedBy
      (fun (r₁ : InterpreterState ctx × Option ControlFlowAction)
           (r₂ : InterpreterState ctx' × Option ControlFlowAction) =>
        r₁.1.isRefinedBy r₂.1 mapping ∧ ControlFlowAction.optionIsRefinedBy r₁.2 r₂.2)
      (interpretOp op state opIn)
      (interpretOp op' state' opIn') := by
  -- If the source interpretation fails, then the refinement is trivial
  by_cases hsource : interpretOp op state opIn = none; simp [hsource, Interp.isRefinedBy]
  -- Source/target operands are defined, and memory is equal.
  have ⟨operands, hSrcOps⟩ : ∃ operands, state.variables.getOperandValues op = some operands := by
    grind [interpretOp]
  obtain ⟨operands', hTgtOps, hOpsRef⟩ :=
    VariableState.getOperandValues_isRefinedBy hState.2 opIn hPreserves.operands hSrcOps
  have hMem : state.memory = state'.memory := hState.1
  -- Add the refinement of `interpretOp'` on `op` with `operands` and `operands'`
  have hPR1 := interpretOp'_monotone (op.getOpType! ctx.raw)
    (op.getProperties! ctx.raw (op.getOpType! ctx.raw)) (op.getResultTypes! ctx.raw)
    operands operands' (op.getSuccessors! ctx.raw) state.memory hOpsRef
  -- Add the equality between `interpretOp'` on `operands'`
  have hInterp'Eq : op'.interpret ctx'.raw operands' state'.memory =
                    op.interpret ctx.raw operands' state.memory := by
     grind [interpretOp'_opType_cast, cases ValueMapping.PreservesOperation]
  /- Do a case analysis on the source interpretation -/
  rcases hsrc : interpretOp op state opIn with _ | (⟨state₂, act⟩ | _)
  · -- If the source interpretation fails, then the refinement is trivial
    simp [Interp.isRefinedBy]
  · /- If the source interpretation returns a new state, we need to prove that (1) the target
       interpretation also returns a new state, and (2) the new states are in the refinement relation. -/
    simp only [Interp.isRefinedBy_ok_target_iff, Prod.exists]
    have ⟨resValues, hinterp', hResValues⟩ :=
      (interpretOp_ok_iff_of_getOperandValues_eq_some hSrcOps).mp hsrc
    simp only [hinterp', Interp.isRefinedBy_ok_target_iff, Prod.exists] at hPR1
    have ⟨resValues', memory'₂, act', hinterp'Tgt, resValuesRef, memoryEq, actRef⟩ := hPR1
    subst memory'₂
    simp only [← hInterp'Eq] at hinterp'Tgt
    simp only [interpretOp, hTgtOps, bind, hinterp'Tgt, liftM, monadLift, MonadLift.monadLift]
    have := interpretOp'_results_conform (opInBounds := opIn') opVerif' (VariableState.getOperandValues_conforms hTgtOps) hinterp'Tgt
    have ⟨v, hv⟩ := (VariableState.setResultValues?_isSome_iff_conforms state'.variables opIn').mp this
    simp only [Interp, hv, pure, Option.some.injEq, UBOr.ok.injEq, Prod.mk.injEq]
    have stateVarRef : state.variables.isRefinedBy state'.variables mapping := by grind [InterpreterState.isRefinedBy]
    grind [InterpreterState.isRefinedBy, VariableState.setResultValues?_isRefinedBy stateVarRef resValuesRef, cases ValueMapping.PreservesOperation]
  · /- If the source interpretation returns UB, then the refinement holds trivially. -/
    simp


/-!
## Monotonicity of `interpretOpList` and `interpretTerminatedOpList`

Lifts the per-operation monotonicity lemma `interpretOp_monotone` to lists of operations
(`interpretOpList` / `interpretTerminatedOpList`), under a *cross-context* interpreter-state
refinement over an *identical* list of operations modulus α-renaming
(`ValueMapping.PreservesOperation`) of operands and results. -/

/-- `interpretOpList` is monotone under a *cross-context* interpreter-state refinement, over an
*identical* slice of a block operation chain (the same `OperationPtr`s, whose intrinsic data agrees
modulo renaming `mapping`). -/
theorem interpretOpList_mono
    {ctx ctx' : WfIRContext OpCode} (hVerif : ctx'.Verified)
    {ops : List OperationPtr}
    (opsInBounds : ∀ op, op ∈ ops → op.InBounds ctx.raw)
    (opsInBounds' : ∀ op, op ∈ ops → op.InBounds ctx'.raw)
    {mapping : ValueMapping ctx ctx'}
    {state : InterpreterState ctx} {state' : InterpreterState ctx'}
    (hState : state.isRefinedBy state' mapping)
    (hPreserves : ∀ op, (h : op ∈ ops) → mapping.PreservesOperation op op) :
    Interp.isRefinedBy
      (fun (r₁ : InterpreterState ctx × Option ControlFlowAction)
           (r₂ : InterpreterState ctx' × Option ControlFlowAction) =>
        r₁.1.isRefinedBy r₂.1 mapping ∧ ControlFlowAction.optionIsRefinedBy r₁.2 r₂.2)
      (interpretOpList ops state) (interpretOpList ops state') := by
  induction ops generalizing state state' with
  | nil => simpa [Interp]
  | cons a l ih =>
    /- Refinement of the state after interpreting the head operation `a`. -/
    have refinesHead := interpretOp_monotone (opsInBounds a (by grind)) (opsInBounds' a (by grind))
      hState (hPreserves a (by grind)) (by grind)
    simp only [interpretOpList_cons]
    /- Case analysis on the interpretation of the head operation `a` in the source. -/
    rcases hsrc : interpretOp a state (opsInBounds a (by grind)) with _ | (⟨s, act⟩ | _)
    · /- Source operation fails: interpreting the list returns `none`, refinement is trivial. -/
      simp [Interp.isRefinedBy]
    · /- Source operation succeeds with new state `s` and action `act`. This means that the target
      operation also succeeds with a refined state `s'` and action `act'`. -/
      simp only [hsrc, Interp.isRefinedBy_ok_target_iff] at refinesHead
      obtain ⟨⟨s', act'⟩, htgt, hsRef, hactRef⟩ := refinesHead
      simp only [htgt]
      /- Case analysis on the action. -/
      cases act
      case none =>
        /- No control-flow action: recurse on the tail, advancing the target invariant past `a`.
        We use the induction to handle the tail. -/
        have hact' : act' = none := by grind [ControlFlowAction.optionIsRefinedBy]
        subst hact'
        simp only
        apply ih (by grind) (by grind) hsRef (by grind)
      case some cf =>
        simp [ControlFlowAction.optionIsRefinedBy] at hactRef
        /- A control-flow action: the list stops here for both the source and the target. -/
        have ⟨cf', hact', hcfRef⟩ : ∃ cf', act' = some cf' ∧ cf.isRefinedBy cf' := by grind
        subst hact'
        simp [Interp, hsRef, ControlFlowAction.optionIsRefinedBy, hcfRef]
    · /- Source operation is UB, which is refined by anything. -/
      simp

/-- `interpretTerminatedOpList` is monotone under a *cross-context* interpreter-state refinement,
over an *identical* list of operations. The proof is derived from `interpretOpList_monotone`, as
`interpretTerminatedOpList` is a wrapper around `interpretOpList` that checks that the list of
operation has reached a terminator. -/
theorem interpretTerminatedOpList_mono
    {ctx ctx' : WfIRContext OpCode} (ctx'Verif : ctx'.Verified)
    {state : InterpreterState ctx} {state' : InterpreterState ctx'}
    {mapping : ValueMapping ctx ctx'}
    (opsInBounds : ∀ op, op ∈ ops → op.InBounds ctx.raw)
    (opsInBounds' : ∀ op, op ∈ ops → op.InBounds ctx'.raw)
    (hState : state.isRefinedBy state' mapping)
    (hFrame : ∀ op, (h : op ∈ ops) → mapping.PreservesOperation op op) :
    Interp.isRefinedBy
      (fun (r₁ : InterpreterState ctx × ControlFlowAction)
           (r₂ : InterpreterState ctx' × ControlFlowAction) =>
        r₁.1.isRefinedBy r₂.1 mapping ∧ r₁.2.isRefinedBy r₂.2)
      (interpretTerminatedOpList ops state) (interpretTerminatedOpList ops state') := by
  have hList := interpretOpList_mono ctx'Verif opsInBounds opsInBounds' hState hFrame
  simp only [interpretTerminatedOpList, bind]
  rcases hsrc : interpretOpList ops state (by grind) with _ | (⟨s, act⟩ | _)
  · simp [Interp.isRefinedBy]
  · simp only [hsrc, Interp.isRefinedBy_ok_target_iff] at hList
    obtain ⟨⟨s', act'⟩, htgt, hsRef, hactRef⟩ := hList
    simp only [htgt]
    /- Case analysis on the action returned by `interpretOpList`. If no action is returned at the
    source, then the refinement is trivial (as interpretation failed in the input). If an action
    is returned, then we derive refinement from the refinement of the action (given by
    `interpretOpList_mono`). -/
    cases act with
    | none =>  simp [Interp.isRefinedBy]
    | some cf =>
      have ⟨cf', hact', hcfRef⟩ : ∃ cf', act' = some cf' ∧ cf.isRefinedBy cf' := by
        cases act' <;> simp_all [ControlFlowAction.optionIsRefinedBy]
      subst hact'
      exact ⟨hsRef, hcfRef⟩
  · exact Interp.isRefinedBy_ub_target

end Veir
