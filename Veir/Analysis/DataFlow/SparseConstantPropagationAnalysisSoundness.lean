module

public import Veir.Analysis.DataFlow.Domains.ConstantSoundness
public import Veir.Analysis.DataFlow.SparseConstantPropagationAnalysis
public import Veir.Interfaces.FoldSoundness
public import Veir.Interpreter.Lemmas
import Veir.Interpreter.Refinement.Lemmas
import all Veir.IR.Basic
import all Veir.Interfaces.ConstantLikeInterfaces
import all Veir.Interfaces.FoldInterfaces

/-!
# Soundness of sparse constant propagation

Local soundness of `SparseConstantPropagation.transfer` (`transfer_sound`): if every
operand lies in `γ` of its fact, every result lies in `γ` of the fact `transfer`
produces.

A real operand may be less defined than its constant fact (poison where the fact
says `5`), so the folder's inputs do not describe it. The proof replaces each such
operand by the fact's value (`refineOperands`), applies the fold contract there
(`foldsTo_sound`), and carries the result back to the real operands by monotonicity
of the interpreter.
-/

public section

namespace Veir

namespace SparseConstantPropagation

/-- Every operand lies in `γ` of its fact, one fact per operand. -/
@[expose]
def OperandsInGamma (facts : Array AbstractConstant) (vs : Array RuntimeValue) : Prop :=
  facts.size = vs.size ∧
    ∀ (j : Nat) (a : AbstractConstant) (v : RuntimeValue),
      facts[j]? = some a → vs[j]? = some v → v ∈ AbstractConstant.γ a

/-- The operands with each constant fact's value in place of its operand. -/
@[expose]
def refineOperands (facts : Array AbstractConstant) (vs : Array RuntimeValue) :
    Array RuntimeValue :=
  Array.ofFn fun (j : Fin vs.size) =>
    match facts[j.val]? with
    | some (.constant c) => c
    | _ => vs[j]

/-- `refineOperands` keeps the number of operands. -/
@[simp]
theorem refineOperands_size (facts : Array AbstractConstant) (vs : Array RuntimeValue) :
    (refineOperands facts vs).size = vs.size := by
  simp [refineOperands]

/-- Substitute `j` is fact `j`'s constant if it has one, else real operand `j`. -/
theorem refineOperands_getElem (facts : Array AbstractConstant) (vs : Array RuntimeValue)
    (j : Nat) (hj : j < vs.size) :
    (refineOperands facts vs)[j]'(by simpa using hj) =
      match facts[j]? with
      | some (.constant c) => c
      | _ => vs[j] := by
  simp [refineOperands]

/-- Each real operand is refined by its substitute. -/
theorem isRefinedBy_refineOperands {facts : Array AbstractConstant} {vs : Array RuntimeValue}
    (hOperands : OperandsInGamma facts vs) : vs ⊒ refineOperands facts vs := by
  refine ⟨by simp, fun j hj => ?_⟩
  rw [getElem!_pos vs j hj, getElem!_pos (refineOperands facts vs) j (by simpa using hj),
    refineOperands_getElem facts vs j hj]
  split
  · next c hc => exact hOperands.2 j _ _ hc (Array.getElem?_eq_getElem hj)
  · exact RuntimeValue.isRefinedBy_refl _

/-- The folder's inputs describe the substitutes exactly. -/
theorem constOperandsAgree_refineOperands {facts : Array AbstractConstant}
    {vs : Array RuntimeValue} (hOperands : OperandsInGamma facts vs) :
    ConstOperandsAgree (constantOperands facts) (refineOperands facts vs) := by
  intro j v hConst
  simp only [constantOperands, Array.getElem?_map, Option.map_eq_some_iff] at hConst
  obtain ⟨a, ha, hv⟩ := hConst
  cases a with
  | constant c =>
    simp only [Option.some.injEq] at hv
    subst hv
    have hj : j < vs.size := hOperands.1 ▸ (Array.getElem?_eq_some_iff.mp ha).1
    rw [Array.getElem?_eq_getElem (by simpa using hj), refineOperands_getElem facts vs j hj, ha]
  | top => simp at hv
  | bottom => simp at hv

/-- The substitutes lie in `γ` of their facts. -/
theorem operandsInGamma_refineOperands {facts : Array AbstractConstant}
    {vs : Array RuntimeValue} (hOperands : OperandsInGamma facts vs) :
    OperandsInGamma facts (refineOperands facts vs) := by
  refine ⟨by simpa using hOperands.1, fun j a v ha hv => ?_⟩
  have hj : j < vs.size := by simpa using (Array.getElem?_eq_some_iff.mp hv).1
  rw [Array.getElem?_eq_getElem (by simpa using hj), refineOperands_getElem facts vs j hj,
    ha] at hv
  simp only [Option.some.injEq] at hv
  cases a with
  | constant c => subst hv; exact AbstractConstant.mem_γ_constant_self c
  | top => exact AbstractConstant.mem_γ_top v
  | bottom =>
    subst hv
    exact hOperands.2 j _ _ ha (Array.getElem?_eq_getElem hj)

/-- `interpretPure` is monotone in its operands wherever `interpretOp'` is. -/
theorem interpretPure_isRefinedBy (opType : OpCode) [InterpretOp'Monotone opType]
    (properties : propertiesOf opType) (resultTypes : Array TypeAttr)
    {vs vs' : Array RuntimeValue} (h : vs ⊒ vs') :
    Interp.isRefinedBy RuntimeValue.arrayIsRefinedBy
      (interpretPure opType properties resultTypes vs)
      (interpretPure opType properties resultTypes vs') := by
  have hMono := interpretOp'_monotone opType properties resultTypes vs vs' #[]
    MemoryState.empty MemoryState.empty h (MemoryState.isRefinedBy_refl _)
  simp only [interpretPure]
  cases hs : interpretOp' opType properties resultTypes vs #[] MemoryState.empty <;>
    cases ht : interpretOp' opType properties resultTypes vs' #[] MemoryState.empty <;>
    simp_all [Interp.isRefinedBy, OperationResult.isRefinedBy]

/-- A fold decision sound for `operands` yields a fact sound for the same outcome. -/
theorem ofFoldDecision_soundFor
    (decision : FoldDecision) (facts : Array AbstractConstant)
    (operands : Array RuntimeValue) (outcome : Interp (Array RuntimeValue)) (i : Nat)
    (hOperands : OperandsInGamma facts operands)
    (hDecision : decision.SoundFor operands outcome i) :
    (AbstractConstant.ofFoldDecision decision facts).SoundFor outcome i := by
  cases outcome with
  | fail _ => trivial
  | ub _ => trivial
  | ok results =>
    simp only [AbstractConstant.SoundFor]
    simp only [FoldDecision.SoundFor] at hDecision
    cases hResult : results[i]? with
    | none => trivial
    | some actual =>
      simp only [hResult] at hDecision
      obtain ⟨claimed, hValue, hRefines⟩ := hDecision
      cases decision with
      | useConstant value =>
        simp only [FoldDecision.valueFor, Option.some.injEq] at hValue
        subst hValue
        exact AbstractConstant.mem_γ_of_isRefinedBy hRefines
          (AbstractConstant.mem_γ_constant_self _)
      | useOperand j =>
        simp only [FoldDecision.valueFor] at hValue
        simp only [AbstractConstant.ofFoldDecision]
        apply AbstractConstant.mem_γ_of_isRefinedBy hRefines
        cases ha : facts[j]? with
        | none => simp
        | some a => simpa [ha] using hOperands.2 j a claimed ha hValue

/--
Soundness of a fold for the real operands: the contract holds for the substitutes,
and monotonicity carries it back.
-/
theorem fold_sound
    (opType : OpCode) [InterpretOp'Monotone opType] (properties : propertiesOf opType)
    (resultTypes : Array TypeAttr) (facts : Array AbstractConstant) (vs : Array RuntimeValue)
    (decisions : Array FoldDecision) (i : Nat) (decision : FoldDecision)
    (hTable : FoldTableSound opType) (hPoison : PropagatesPoisonSound opType)
    (hOperands : OperandsInGamma facts vs)
    (hFold : OpCode.foldsTo opType properties resultTypes (constantOperands facts)
      = some decisions)
    (hDecision : decisions[i]? = some decision) :
    (AbstractConstant.ofFoldDecision decision facts).SoundFor
      (interpretPure opType properties resultTypes vs) i := by
  have hExact := foldsTo_sound opType properties resultTypes (refineOperands facts vs)
    (constantOperands facts) decisions i decision hTable hPoison
    (constOperandsAgree_refineOperands hOperands)
    (by simp [constantOperands, hOperands.1]) hFold hDecision
  exact AbstractConstant.soundFor_of_isRefinedBy
    (interpretPure_isRefinedBy opType properties resultTypes
      (isRefinedBy_refineOperands hOperands))
    (ofFoldDecision_soundFor decision facts _ _ i
      (operandsInGamma_refineOperands hOperands) hExact)

/--
Local soundness of the constant-propagation transfer function.

If every operand lies in `γ` of its fact, every result lies in `γ` of the fact
`transfer` produces (`AbstractConstant.SoundFor`), whenever interpretation succeeds;
UB and interpreter failure constrain nothing.

Hypotheses:
* `InterpretOp'Monotone` — the opcode's interpreter is monotone under refinement;
* `hTable`, `hPoison` — per-opcode obligations of `foldsTo_sound`;
* `hArity` — as many operands as the op has;
* `hConstSuccessors` — a constant-like operation has no successors, so the
  interpretation that `ValuePtr.constantValue` runs agrees with `interpretPure`.
-/
theorem transfer_sound
    (op : OperationPtr) (irCtx : WfIRContext OpCode)
    [InterpretOp'Monotone (op.getOpType! irCtx.raw)]
    (abstractOperands : Array AbstractConstant) (concreteOperands : Array RuntimeValue)
    (hTable : FoldTableSound (op.getOpType! irCtx.raw))
    (hPoison : PropagatesPoisonSound (op.getOpType! irCtx.raw))
    (hOperands : OperandsInGamma abstractOperands concreteOperands)
    (hArity : concreteOperands.size = op.getNumOperands! irCtx.raw)
    (hConstSuccessors : (op.getOpType! irCtx.raw).isConstantLike = true →
      op.getSuccessors! irCtx.raw = #[])
    (i : Nat) :
    ((transfer op abstractOperands irCtx)[i]?.getD ⊤).SoundFor
      (interpretPure (op.getOpType! irCtx.raw)
        (op.getProperties! irCtx.raw (op.getOpType! irCtx.raw))
        (op.getResultTypes! irCtx.raw) concreteOperands) i := by
  have hTop : ∀ n, ((Array.replicate n (⊤ : AbstractConstant))[i]?.getD ⊤) = ⊤ := by
    intro n
    rw [Array.getElem?_replicate]
    split <;> rfl
  by_cases hRegions : op.getNumRegions! irCtx.raw ≠ 0
  · rw [show transfer op abstractOperands irCtx =
        Array.replicate (op.getNumResults! irCtx.raw) ⊤ by simp [transfer, hRegions], hTop]
    exact AbstractConstant.soundFor_top _ i
  have hRegions0 : op.getNumRegions! irCtx.raw = 0 := by simpa using hRegions
  by_cases hBot : abstractOperands.any (· = ⊥)
  · -- No operand lies in `γ ⊥`, so this case is vacuous.
    exfalso
    obtain ⟨j, hj, hjBot⟩ := Array.any_eq_true.mp hBot
    have hjConcrete : j < concreteOperands.size := hOperands.1 ▸ hj
    have hMem := hOperands.2 j _ _ (Array.getElem?_eq_getElem hj)
      (Array.getElem?_eq_getElem hjConcrete)
    simp only [decide_eq_true_eq] at hjBot
    rw [hjBot] at hMem
    exact AbstractConstant.not_mem_γ_bot _ hMem
  by_cases hConst : (op.getOpType! irCtx.raw).isConstantLike = true
  · -- Port of the constant-like branch of `transferExact_sound` on
    -- `constant-propagation-proofs` (SparseConstantPropagationSoundness.lean:228-264),
    -- with `AbstractConstant.exact` renamed to `AbstractConstant.constant` and
    -- `mem_γ_exact_self` to `mem_γ_constant_self`.
    have hSuccessors := hConstSuccessors hConst
    rw [show transfer op abstractOperands irCtx =
        (op.getResults! irCtx.raw).map (fun result =>
          (result.constantValue irCtx.raw).map AbstractConstant.constant |>.getD ⊤) by
          simp [transfer, hRegions0, hBot, hConst]]
    by_cases hi : ¬ i < op.getNumResults! irCtx.raw
    · have hNone : (op.getResults! irCtx.raw)[i]? = none := by simp; omega
      simp [Array.getElem?_map, hNone]
    simp only [Decidable.not_not] at hi
    rw [Array.getElem?_map, Array.getElem?_eq_getElem (by simpa using hi), Option.map_some,
      Option.getD_some, OperationPtr.getResults!.getElem_eq_getResult hi]
    have hConstOp : op.isConstantLike irCtx.raw = true := hConst
    by_cases hNum : op.getNumOperands! irCtx.raw ≠ 0
    · simp [ValuePtr.constantValue, OperationPtr.getResult, hNum]
    simp only [Decidable.not_not] at hNum
    have hEmpty : concreteOperands = #[] := Array.eq_empty_of_size_eq_zero (by omega)
    subst hEmpty
    simp only [ValuePtr.constantValue, OperationPtr.getResult, hConstOp, hNum,
      OperationPtr.interpret, hSuccessors, interpretPure, not_true_eq_false, ite_false, ne_eq]
    cases interpretOp' (op.getOpType! irCtx.raw)
        (op.getProperties! irCtx.raw (op.getOpType! irCtx.raw))
        (op.getResultTypes! irCtx.raw) #[] #[] MemoryState.empty with
    | fail _ => exact AbstractConstant.soundFor_fail _ i
    | ub _ => exact AbstractConstant.soundFor_ub _ i
    | ok triple =>
      obtain ⟨results, _, action⟩ := triple
      cases action with
      | some _ => exact AbstractConstant.soundFor_top _ i
      | none =>
        simp only [Interp.map_ok, AbstractConstant.SoundFor]
        cases hResult : results[i]? with
        | none => trivial
        | some actual =>
          simp only [Option.map_some, Option.getD_some]
          exact AbstractConstant.mem_γ_constant_self actual
  by_cases hInBounds : op.InBounds irCtx.raw
  · cases hFold : op.foldsTo irCtx hInBounds (constantOperands abstractOperands) with
    | none =>
      rw [show transfer op abstractOperands irCtx =
          Array.replicate (op.getNumResults! irCtx.raw) ⊤ by
            simp [transfer, hRegions0, hBot, hConst, hInBounds, hFold], hTop]
      exact AbstractConstant.soundFor_top _ i
    | some decisions =>
      rw [show transfer op abstractOperands irCtx =
          decisions.map (fun decision =>
            AbstractConstant.ofFoldDecision decision abstractOperands) by
            simp [transfer, hRegions0, hBot, hConst, hInBounds, hFold]]
      cases hDecision : decisions[i]? with
      | none => simp [hDecision]
      | some decision =>
        simp only [Array.getElem?_map, hDecision, Option.map_some, Option.getD_some]
        simp only [OperationPtr.foldsTo] at hFold
        simp [guard, Option.bind_eq_some_iff] at hFold
        obtain ⟨_, hFold⟩ := hFold
        rw [← OperationPtr.getProperties!_eq_getProperties hInBounds (by grind),
          ← OperationPtr.getResultTypes!_eq_getResultTypes hInBounds,
          ← OperationPtr.getOpType!_eq_getOpType hInBounds] at hFold
        exact fold_sound _ _ _ abstractOperands concreteOperands decisions i decision
          hTable hPoison hOperands hFold hDecision
  · rw [show transfer op abstractOperands irCtx =
        Array.replicate (op.getNumResults! irCtx.raw) ⊤ by
          simp [transfer, hRegions0, hBot, hConst, hInBounds], hTop]
    exact AbstractConstant.soundFor_top _ i

end SparseConstantPropagation

end Veir
