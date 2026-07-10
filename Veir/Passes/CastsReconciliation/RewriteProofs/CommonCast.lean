import Lean
import Veir.PatternRewriter.Basic
import Veir.Interpreter
import Veir.IR.WellFormed
import Veir.Passes.Matching
import Veir.Rewriter.WfRewriter
import Veir.PatternRewriter.Semantics
import Veir.Verifier
import Veir.Data.Casting
import Veir.Passes.CastsReconciliation.Reconciliation
import Veir.Passes.InstructionSelection.RewriteProofs.CommonMatchEqns
import Veir.Passes.InstructionSelection.RewriteProofs.CommonBaseLemmas

/-! ## Pre-generated match equations for the reconciliation patterns

`split`/`grind` realize a matcher's `match_n.eq_k` / `match_n.congr_eq_k` lemmas on demand, in
whichever module first needs them, so two sibling proof modules that both case on the patterns of
`Reconciliation.lean` would each bake a private copy into their olean and clash on import.
Generating them once here — in the module every reconciliation proof imports — gives them a single
shared copy. See `InstructionSelection.RewriteProofs.CommonMatchEqns` for the same trick. -/

open Lean Meta in
run_meta do
  let env ← getEnv
  for anchor in [``Veir.reconcilePairingCastLocal] do
    let some modIdx := env.getModuleIdxFor? anchor
      | throwError "expected `{anchor}` to be imported"
    for n in env.header.moduleData[modIdx.toNat]!.constNames do
      if isMatcherCore env n then
        discard <| Match.getEquationsFor n
        discard <| Match.genMatchCongrEqns n

namespace Veir

/-!
# Shared machinery for the `reconcile-cast` correctness proofs

`builtin.unrealized_conversion_cast` is the only operation the `reconcile-cast` patterns match, and
every pattern reasons about *composing* two of them. This file factors that out:

- `castRuntimeValue` is the interpreter's cast arm as a standalone function on runtime values, and
  `interpretOp'_cast_eq` shows the interpreter agrees with it.
- `castOp_interpretOp_unfold` unfolds one successful interpretation of a cast op into
  `castRuntimeValue` applied to its operand's value.
- `castOp_getVar?_of_EquationLemmaAt` is the graph lemma for the *inner* cast of a round trip: at a
  program point dominated by the inner cast, the state already holds its computed value.
-/

/-- The interpreter's semantics of `builtin.unrealized_conversion_cast` at result type `resType`,
as a function on runtime values. `none` means the cast is not defined for this type/value pair.
Mirrors the `.builtin .unrealized_conversion_cast` arm of `interpretOp'`. -/
def castRuntimeValue (resType : TypeAttr) (v : RuntimeValue) : Option RuntimeValue :=
  match resType.val, v with
  | .registerType _, .int _bw val => some (.reg (LLVM.Int.toReg val))
  | .registerType _, .byte _bw val => some (.reg (LLVM.Byte.toReg val))
  | .registerType _, .addr val => some (.reg ⟨val.toNat⟩)
  | .integerType resBw, .reg val => some (.int resBw.bitwidth (RISCV.Reg.toInt val resBw.bitwidth))
  | .byteType resBw, .reg val => some (.byte resBw.bitwidth (RISCV.Reg.toByte val resBw.bitwidth))
  | .llvmPointerType _, .reg val => some (.addr ⟨val.val⟩)
  | _, _ => none

/-- The interpreter's cast arm computes `castRuntimeValue` at the (single) declared result type. -/
theorem interpretOp'_cast_eq {props : HasOpInfo.propertiesOf (OpCode.builtin .unrealized_conversion_cast)}
    {resType : TypeAttr} {resultTypes : Array TypeAttr} {v : RuntimeValue}
    {blockOperands : Array BlockPtr} {mem : MemoryState}
    (hRes : resultTypes[0]? = some resType) :
    interpretOp' (.builtin .unrealized_conversion_cast) props resultTypes #[v] blockOperands mem
      = match castRuntimeValue resType v with
        | some r => some (.ok (#[r], mem, none))
        | none => none := by
  obtain ⟨a, ha⟩ := resType
  simp only [interpretOp', hRes, castRuntimeValue]
  cases a <;> cases v <;> simp_all [pure, Interp]

/-- `builtin.unrealized_conversion_cast` is pure: its interpretation neither reads nor writes
memory. -/
theorem OperationPtr.Pure.builtin_cast {op : OperationPtr} {ctx : IRContext OpCode}
    (hType : op.getOpType! ctx = .builtin .unrealized_conversion_cast) : op.Pure ctx := by
  unfold OperationPtr.Pure
  rw [hType]
  intro operands memory₁ memory₂
  simp only [interpretOp']
  repeat' split
  all_goals first
    | rfl
    | simp [Interp.map, Option.map, UBOr.map, pure, bind, Option.bind]

/-- Untyped analogue of `LocalRewritePattern.exists_refined_int_getVar?`: a value `v` that is not
one of the matched op's results maps to itself through `LocalRewritePattern.mapping`, so its
source-state value is refined by its target-state value, whatever their common shape. -/
theorem LocalRewritePattern.exists_refined_getVar?
    {ctx : WfIRContext OpCode}
    {ipIn : ip.InBounds ctx.raw}
    {pattern : LocalRewritePattern OpCode}
    {hpattern : pattern ctx op = some (newCtx, some (newOps, newValues))}
    {hreturn : pattern.ReturnValuesInBounds} {hreturn₂ : pattern.ReturnValues}
    {hreturn₃ : pattern.ReturnCtxChanges}
    {state : InterpreterState ctx} {state' : InterpreterState newCtx}
    (valueRefinement : state.variables.isRefinedByAt state'.variables
      (LocalRewritePattern.mapping hpattern hreturn hreturn₂ hreturn₃) (.at ip) (.at ip) ipIn ipIn')
    (state'Dom : state'.DefinesDominating ip ipIn')
    (vIn : v.InBounds ctx.raw)
    (hxVal : state.variables.getVar? v = some sv)
    (hDomCtx : v.dominatesIp ip ctx) (hDom' : v.dominatesIp ip newCtx)
    (hNotRes : v ∉ op.getResults! ctx.raw) :
    ∃ tv, state'.variables.getVar? v = some tv ∧ sv ⊒ tv := by
  have ⟨tv, hTv⟩ := InterpreterState.DefinesDominating.exists_getVar_of_dominatesIp state'Dom
      (hreturn₃.valuePtr_inBounds hpattern vIn) hDom'
  refine ⟨tv, hTv, ?_⟩
  grind [LocalRewritePattern.mapping, valueRefinement v]

/-- Unfold one successful interpretation of a `builtin.unrealized_conversion_cast`: it reads its
operand's runtime value `v`, binds its result to `castRuntimeValue resType v` (which therefore
must be defined), and touches neither memory nor control flow. Applied at `newState := state` this
also unfolds the `EquationHolds` fact of a cast that dominates the match point. -/
theorem castOp_interpretOp_unfold {ctx : WfIRContext OpCode} {castOp : OperationPtr}
    {operand : ValuePtr} {resType : TypeAttr} {state newState : InterpreterState ctx} {cf}
    (inBounds : castOp.InBounds ctx.raw)
    (hOpType : castOp.getOpType! ctx.raw = .builtin .unrealized_conversion_cast)
    (hNumResults : castOp.getNumResults! ctx.raw = 1)
    (hOperands : castOp.getOperands! ctx.raw = #[operand])
    (hResType : ((castOp.getResult 0).get! ctx.raw).type = resType)
    (hinterp : interpretOp castOp state inBounds = some (.ok (newState, cf))) :
    ∃ v r, state.variables.getVar? operand = some v ∧
      castRuntimeValue resType v = some r ∧
      state.memory = newState.memory ∧
      newState.variables.getVar? (castOp.getResult 0) = some r ∧
      cf = none := by
  have hNumOperands : castOp.getNumOperands! ctx.raw = 1 := by
    simp [← OperationPtr.getOperands!.size_eq_getNumOperands!, hOperands]
  have hOperandEq : operand = (castOp.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  -- The (single) declared result type is `resType`.
  have hResTypes0 : (castOp.getResultTypes! ctx.raw)[0]? = some resType := by
    have hsz : (castOp.getResultTypes! ctx.raw).size = 1 := by
      rw [OperationPtr.getResultTypes!.size_eq_getNumResults!, hNumResults]
    have helem := OperationPtr.getResultTypes!.getElem!_eq (op := castOp) (ctx := ctx.raw)
      (index := 0) (by omega)
    rw [Array.getElem?_eq_getElem (by omega),
      show (castOp.getResultTypes! ctx.raw)[0] = (castOp.getResultTypes! ctx.raw)[0]! from by grind,
      helem, hResType]
  -- Read the operand's value out of the successful interpretation.
  obtain ⟨operandValues, _, _, _, hOperandValues, _⟩ := interpretOp_some_iff.mp hinterp
  simp only [VariableState.getOperandValues] at hOperandValues
  have hsize : 0 < (castOp.getOperands! ctx.raw).size := by
    rw [OperationPtr.getOperands!.size_eq_getNumOperands!]; omega
  obtain ⟨v, hv⟩ :=
    Array.exists_mapM_option_eq_some_iff.mp ⟨operandValues, hOperandValues⟩ 0 hsize
  have hgetVar : state.variables.getVar? operand = some v := by
    rw [hOperandEq,
      show (castOp.getOperands! ctx.raw)[0]! = (castOp.getOperands! ctx.raw)[0] from by grind]
    exact hv
  have hOperand0 : castOp.getOperand! ctx.raw 0 = operand := by
    rw [hOperandEq]
    grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOpVals : state.variables.getOperandValues castOp = some #[v] := by
    rw [VariableState.getOperandValues_eq_some_iff]
    refine ⟨by simp [hNumOperands], fun i hi => ?_⟩
    rw [hNumOperands] at hi
    obtain rfl : i = 0 := by omega
    simpa [hOperand0] using hgetVar
  -- With the value in hand, unfold the cast's interpretation into `castRuntimeValue`.
  rw [interpretOp_some_iff] at hinterp
  obtain ⟨operandValues', resValues, mem', varState', hOV, hInterp', hSet, hNew⟩ := hinterp
  rw [hOpVals, Option.some.injEq] at hOV
  subst hOV
  simp only [OperationPtr.interpret] at hInterp'
  rw [hOpType, interpretOp'_cast_eq hResTypes0] at hInterp'
  obtain ⟨r, hCast⟩ : ∃ r, castRuntimeValue resType v = some r := by
    cases hc : castRuntimeValue resType v with
    | none => rw [hc] at hInterp'; simp at hInterp'
    | some r => exact ⟨r, rfl⟩
  rw [hCast] at hInterp'
  obtain ⟨rfl, rfl, rfl⟩ : resValues = #[r] ∧ mem' = state.memory ∧ cf = none := by grind
  subst hNew
  refine ⟨v, r, hgetVar, hCast, rfl, ?_, rfl⟩
  rw [VariableState.getVar?_getResult_of_setResultValues? (by rw [hNumResults]; omega) hSet]
  simp

/-! ## The packaged graph lemma for the inner cast of a round trip -/

set_option maxHeartbeats 1000000 in
/-- Semantic content of the *inner* cast of a round trip: `input` is an operand of `op` and is
defined by a cast operation `castPtr.op` with operand `parentInput`. In any source state
satisfying `EquationLemmaAt` before `op`, that inner cast has already been interpreted, so
`input`'s runtime value is `castRuntimeValue` (at `input`'s type) of `parentInput`'s value. The
accompanying structural facts are what a `PreservesSemantics` proof needs to read `parentInput`'s
refined value in the target state. -/
theorem castOp_getVar?_of_EquationLemmaAt {ctx : WfIRContext OpCode}
    (ctxDom : ctx.Dom)
    {op : OperationPtr} (opInBounds : op.InBounds ctx.raw)
    {state : InterpreterState ctx}
    (stateWf : state.EquationLemmaAt (InsertPoint.before op) (by grind))
    {castPtr : OpResultPtr} {parentInput : ValuePtr}
    (hMatch : matchCastOp castPtr.op ctx.raw = some parentInput)
    (hOperand : ValuePtr.opResult castPtr ∈ op.getOperands! ctx.raw) :
    ∃ v r, state.variables.getVar? parentInput = some v ∧
      castRuntimeValue ((ValuePtr.opResult castPtr).getType! ctx.raw) v = some r ∧
      state.variables.getVar? (ValuePtr.opResult castPtr) = some r ∧
      parentInput.dominatesIp (InsertPoint.before op) ctx ∧
      parentInput.InBounds ctx.raw ∧
      parentInput ∉ op.getResults! ctx.raw := by
  obtain ⟨hCastType, hCastNumResults, hCastOperands⟩ := matchCastOp_implies hMatch
  have hParentMem : parentInput ∈ castPtr.op.getOperands! ctx.raw := by rw [hCastOperands]; simp
  -- The inner cast is in bounds and `input` is its unique result.
  have hInputIn : (ValuePtr.opResult castPtr).InBounds ctx.raw := by
    grind [OperationPtr.getOperands!]
  have hCastOpIn : castPtr.op.InBounds ctx.raw := by grind [OpResultPtr.InBounds]
  have hCastIdx : castPtr.index < castPtr.op.getNumResults! ctx.raw := by
    grind [OpResultPtr.inBounds_OperationPtr_getNumResults!]
  have hCastEq : castPtr = castPtr.op.getResult 0 := by
    have hidx : castPtr.index = 0 := by omega
    cases castPtr
    simp only [OperationPtr.getResult, OpResultPtr.mk.injEq]
    exact ⟨trivial, hidx⟩
  have hResType : ((castPtr.op.getResult 0).get! ctx.raw).type
      = (ValuePtr.opResult castPtr).getType! ctx.raw := by
    rw [hCastEq]; rfl
  -- Dominance: the inner cast strictly dominates `op`, so it has been interpreted into `state`.
  have hCastDefines : (ValuePtr.opResult castPtr).getDefiningOp! ctx.raw = some castPtr.op := by
    have hOwner := (ctx.wellFormed.operations castPtr.op hCastOpIn).result_owner 0 (by grind)
    grind [ValuePtr.getDefiningOp!]
  have hCastSDom : castPtr.op.strictlyDominates op ctx :=
    OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands! ctxDom
      hCastDefines hOperand
  have hCastDomIp : castPtr.op.dominatesIp (InsertPoint.before op) ctx := by grind
  have hCastPure : castPtr.op.Pure ctx.raw := OperationPtr.Pure.builtin_cast hCastType
  obtain ⟨cfC, hInterpCast⟩ := stateWf castPtr.op hCastOpIn hCastPure hCastDomIp
  -- Unfold the inner cast's interpretation (`newState := state`).
  obtain ⟨v, r, hParentVal, hCast, -, hCastResVal, -⟩ :=
    castOp_interpretOp_unfold hCastOpIn hCastType hCastNumResults hCastOperands hResType hInterpCast
  refine ⟨v, r, hParentVal, hCast, by rw [hCastEq]; exact hCastResVal, ?_, ?_, ?_⟩
  · -- `parentInput` dominates the inner cast, hence `op`.
    exact ValuePtr.dominatesIp_before_of_strictlyDominates
      (ctxDom.operand_dominates_op hCastOpIn hParentMem) hCastSDom
  · grind [OperationPtr.getOperands!]
  · exact IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom
      (OperationPtr.dominates_of_strictlyDominates hCastSDom) parentInput hParentMem

end Veir
