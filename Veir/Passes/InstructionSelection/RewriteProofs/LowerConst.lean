import Veir.PatternRewriter.Basic
import Veir.Interpreter
import Veir.IR.WellFormed
import Veir.Passes.Matching
import Veir.Rewriter.WfRewriter
import Veir.PatternRewriter.Semantics
import Veir.Verifier
import Veir.Data.LLVM.Int.Lemmas
import Veir.Data.RISCV.Reg.Lemmas
import Veir.Data.Casting
import Veir.Passes.InstructionSelection.RISCV64
import Veir.Passes.InstructionSelection.RewriteProofs.CommonMatchEqns
import Veir.Passes.InstructionSelection.RewriteProofs.CommonTactics
import Veir.Passes.InstructionSelection.RewriteProofs.CommonBaseLemmas
import Veir.Passes.InstructionSelection.RewriteProofs.CommonForwardInterpret

namespace Veir

/-! ## Correctness of `constant_local` (`llvm.mlir.constant` → `riscv.li` → cast) -/

/-- Nullary `riscv.li` specialization of `interpretOp_forward`: a `riscv.li` op with no operands and
a single `!riscv.reg` result binds that result to `.reg (Data.RISCV.li (BitVec.ofInt 64 imm))`,
where `imm` is the op's immediate property value, leaving memory and every other value unchanged. -/
theorem interpretOp_riscv_li_forward
    {ctx : WfIRContext OpCode} {theOp : OperationPtr} {state : InterpreterState ctx}
    {inBounds : theOp.InBounds ctx.raw} {rt : RegisterType} {hIsTy}
    {props : HasDialectOpInfo.propertiesOf Riscv.li}
    (hType : theOp.getOpType! ctx.raw = .riscv .li)
    (hProps : theOp.getProperties! ctx.raw (.riscv .li) = props)
    (hOperands : theOp.getOperands! ctx.raw = #[])
    (hResTypes : theOp.getResultTypes! ctx.raw = #[⟨.registerType rt, hIsTy⟩]) :
    ∃ state', interpretOp theOp state inBounds = some (.ok (state', none)) ∧
      state'.memory = state.memory ∧
      state'.variables.getVar? (ValuePtr.opResult (theOp.getResult 0))
        = some (.reg (Data.RISCV.li (BitVec.ofInt 64 props.value.value))) ∧
      (∀ v', v' ∉ theOp.getResults! ctx.raw →
        state'.variables.getVar? v' = state.variables.getVar? v') := by
  obtain ⟨state', hI, hMem, hVal⟩ :=
    interpretOp_forward (op := theOp) (state := state) (inBounds := inBounds)
      (vals := #[]) (results := #[.reg (Data.RISCV.li (BitVec.ofInt 64 props.value.value))])
      (mem' := state.memory)
      (by simp [VariableState.getOperandValues, hOperands])
      (by simp only [OperationPtr.interpret]
          rw [hType]
          simp only [interpretOp', Riscv.interpretOp', hProps, Interp]
          rfl)
      (by simp [RuntimeValue.ArrayConforms, hResTypes, RuntimeValue.Conforms])
  have hNRes : 0 < theOp.getNumResults! ctx.raw := by
    rw [← OperationPtr.getResultTypes!.size_eq_getNumResults!, hResTypes]; simp
  grind

/-- The `riscv.li` lowering of an `llvm.mlir.constant` of result width `retW ≤ 64` is correct: the
64-bit immediate `BitVec.ofInt 64 c`, cast back to `i{retW}`, equals the LLVM constant. -/
theorem constant_isRefinedBy_toInt_li {retW : Nat} (hle : retW ≤ 64) (c : Int) :
    Data.LLVM.Int.constant retW c
      ⊒ RISCV.Reg.toInt (Data.RISCV.li (BitVec.ofInt 64 c)) retW := by
  rw [Data.LLVM.Int.isRefinedBy_iff]
  refine ⟨fun _ => toInt_isPoison, fun _ _ => ?_⟩
  rw [Data.LLVM.Int.getValue_constant, toInt_getValue]
  simp only [Data.RISCV.li]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofInt]
  have hdvd : ((2 ^ retW : Nat) : Int) ∣ ((2 ^ 64 : Nat) : Int) := by
    exact_mod_cast Nat.pow_dvd_pow 2 hle
  have key : c % ((2 ^ 64 : Nat) : Int) % ((2 ^ retW : Nat) : Int) = c % ((2 ^ retW : Nat) : Int) :=
    Int.emod_emod_of_dvd c hdvd
  have h64 : (2 ^ 64 : Nat) ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos 64)
  have hnn : (0 : Int) ≤ c % ((2 ^ 64 : Nat) : Int) :=
    Int.emod_nonneg c (by exact_mod_cast h64)
  rw [← key, Int.toNat_emod hnn, Int.toNat_natCast]
  exact_mod_cast Nat.zero_le _

set_option maxHeartbeats 1000000 in
/-- Correctness of the `constant_local` lowering: `llvm.mlir.constant` (integer) lowers to
`riscv.li` of the 64-bit immediate followed by a cast back to the (`≤ 64`-bit) integer result
type, and the round trip refines the LLVM constant. -/
theorem constant_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics constant_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, constant_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [Option.bind_eq_bind, pure, Option.bind_eq_bind] at hpattern
  -- Peel the matcher: only the `some` branch can reach the `some (...)` RHS.
  have hMatchSome : (matchConstantIntOp op ctx.raw).isSome := by
    cases hM : matchConstantIntOp op ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨const, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  -- Syntactic + verification facts.
  have ⟨hOpType, hPropVal⟩ := matchConstantIntOp_implies hMatch
  have opVerif : op.Verified ctx opInBounds := by grind
  have ⟨hNRes, hNOper, hNSucc, hNReg⟩ := OperationPtr.Verified.llvm_mlir__constant opVerif hOpType
  -- First width guard (on `const.type.bitwidth`) is false.
  peelSplittableCondition [hW1] hpattern
  -- Resolve the result-type destructuring match: the result type is an integer type.
  obtain ⟨retTy, hResIntTy⟩ :=
    OperationPtr.Verified.llvm_mlir__constant_resultType opVerif hOpType hPropVal
  rw [hResIntTy] at hpattern
  simp only [] at hpattern
  -- Second width guard (on `retTy.bitwidth`) is false.
  peelSplittableCondition [hW2] hpattern
  have hRetLe : retTy.bitwidth ≤ 64 := by
    simp only [not_and, Decidable.not_not] at hW2 ⊢
    omega
  -- The op's result types, for the source interpretation.
  have hResTypes : op.getResultTypes! ctx.raw = #[⟨Attribute.integerType retTy, (by grind)⟩] := by
    apply Array.ext
    · simp [OperationPtr.getResultTypes!.size_eq_getNumResults!, hNRes]
    · intro i h1 h2
      simp only [OperationPtr.getResultTypes!.size_eq_getNumResults!, hNRes] at h1
      obtain rfl : i = 0 := by omega
      simp only [OperationPtr.getResultTypes!.getElem_eq, Array.getElem_singleton]
      exact Subtype.ext hResIntTy
  -- Source value: `op`'s single result is `constant retTy.bitwidth const.value`.
  have hOpVals : state.variables.getOperandValues op = some #[] := by
    rw [VariableState.getOperandValues_eq_some_iff]
    exact ⟨by simp [hNOper], fun i hi => by rw [hNOper] at hi; omega⟩
  rw [interpretOp_some_iff] at hinterp
  obtain ⟨ov, resValues, mem', vs', hOV, hInterp', hSet, hNew⟩ := hinterp
  rw [hOpVals, Option.some.injEq] at hOV
  subst hOV
  simp only [OperationPtr.interpret] at hInterp'
  rw [hOpType] at hInterp'
  simp only [interpretOp', Llvm.interpretOp', hResTypes, hPropVal] at hInterp'
  obtain ⟨rfl, rfl, rfl⟩ :
      resValues = #[RuntimeValue.int retTy.bitwidth
        (Data.LLVM.Int.constant retTy.bitwidth const.value)] ∧ mem' = state.memory ∧ cf = none := by
    simp only [Interp, pure] at hInterp'
    grind
  have hResVal : newState.variables.getVar? (op.getResult 0)
      = some (.int retTy.bitwidth (Data.LLVM.Int.constant retTy.bitwidth const.value)) := by
    rw [hNew, VariableState.getVar?_getResult_of_setResultValues? (by rw [hNRes]; omega) hSet]; simp
  -- Source values array.
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hResVal] at hsourceValues
  subst sourceValues
  -- Peel the two created ops: the `riscv.li` and the cast-back.
  peelOpCreation hpattern ctx₁ liOp hLi
  rw [WfRewriter.createOp!_none_eq (by clear hpattern; grind) (by clear hpattern; simp)
    (by clear hpattern; simp)] at hLi
  peelOpCreation hpattern ctx₂ castOp hCast
  rw [WfRewriter.createOp!_none_eq (by clear hpattern; grind) (by clear hpattern; simp)
    (by clear hpattern; simp)] at hCast
  cleanupHpattern hpattern
  -- Structural facts about the two created ops in the final context `ctx₂`.
  have hLiType : liOp.getOpType! ctx₂.raw = .riscv .li := by grind
  have hCastType : castOp.getOpType! ctx₂.raw = .builtin .unrealized_conversion_cast := by grind
  have hLiOperands : liOp.getOperands! ctx₂.raw = #[] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hLi (operation := liOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCast (operation := liOp)]
  have hCastOperands : castOp.getOperands! ctx₂.raw = #[ValuePtr.opResult (liOp.getResult 0)] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hCast (operation := castOp)]
  have hLiProps : liOp.getProperties! ctx₂.raw (.riscv .li) = { value := const } := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hLi (operation := liOp),
      OperationPtr.getProperties!_WfRewriter_createOp_ne hCast]
  have hLiResTypes : liOp.getResultTypes! ctx₂.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hLi (operation := liOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCast (operation := liOp)]
  have hCastResTypes : castOp.getResultTypes! ctx₂.raw
      = #[⟨Attribute.integerType retTy, (by grind)⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCast (operation := castOp)]
  -- Interpretation tail: execute `interpretOpList [liOp, castOp]` in `state'`.
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
    interpretOp_riscv_li_forward (state := state') (inBounds := by grind)
      hLiType hLiProps hLiOperands hLiResTypes
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
    interpretOp_castBack_forward (state := s₁) (inBounds := by grind)
      hCastType hCastOperands hCastResTypes hRes₁
  refine ⟨s₂, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, liftM, monadLift, MonadLift.monadLift, Interp]
  · refine ⟨#[RuntimeValue.int retTy.bitwidth
        (RISCV.Reg.toInt (Data.RISCV.li (BitVec.ofInt 64 const.value)) retTy.bitwidth)], ?_, ?_⟩
    · simp [hRes₂, Option.bind, Option.map]
    · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
        ⟨rfl, by simpa using constant_isRefinedBy_toInt_li hRetLe const.value⟩

/-! ## Correctness of `poisonConst_local` (`llvm.mlir.poison` → `riscv.li 0` → cast) -/

/-- The `llvm.mlir.poison` value (which is poison) is refined by any concretisation, in particular
by the round trip through `riscv.li 0`. -/
theorem mlir_poison_isRefinedBy {w : Nat} (r : Data.RISCV.Reg) :
    Data.LLVM.Int.mlir_poison w ⊒ RISCV.Reg.toInt r w := by
  rw [Data.LLVM.Int.isRefinedBy_iff]
  refine ⟨fun h => ?_, fun h _ => ?_⟩ <;> simp [Data.LLVM.Int.isPoison_poison] at h

set_option maxHeartbeats 1000000 in
/-- Correctness of the `poisonConst_local` lowering: `llvm.mlir.poison` (integer) lowers to
`riscv.li 0` followed by a cast back to the integer result type; the source value is poison, so it
is refined by the round trip. -/
theorem poisonConst_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics poisonConst_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, poisonConst_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [Option.bind_eq_bind, pure, Option.bind_eq_bind] at hpattern
  -- Peel the matcher.
  have hMatchSome : (matchPoison op ctx.raw).isSome := by
    cases hM : matchPoison op ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨u, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  have ⟨hOpType, hNOper, hNRes⟩ := matchPoison_implies hMatch
  -- The op's single result type, as an array.
  have hResTypesArr : op.getResultTypes! ctx.raw = #[((op.getResult 0).get! ctx.raw).type] := by
    apply Array.ext
    · simp [OperationPtr.getResultTypes!.size_eq_getNumResults!, hNRes]
    · intro i h1 h2
      simp only [OperationPtr.getResultTypes!.size_eq_getNumResults!, hNRes] at h1
      obtain rfl : i = 0 := by omega
      simp [OperationPtr.getResultTypes!.getElem_eq]
  -- Source value: unfold the interpretation of `llvm.mlir.poison`; the result type must be integer.
  have hOpVals : state.variables.getOperandValues op = some #[] := by
    rw [VariableState.getOperandValues_eq_some_iff]
    exact ⟨by simp [hNOper], fun i hi => by rw [hNOper] at hi; omega⟩
  rw [interpretOp_some_iff] at hinterp
  obtain ⟨ov, resValues, mem', vs', hOV, hInterp', hSet, hNew⟩ := hinterp
  rw [hOpVals, Option.some.injEq] at hOV
  subst hOV
  simp only [OperationPtr.interpret] at hInterp'
  rw [hOpType] at hInterp'
  simp only [interpretOp', Llvm.interpretOp', hResTypesArr] at hInterp'
  rw [show (#[((op.getResult 0).get! ctx.raw).type] : Array TypeAttr)[0]?
      = some ((op.getResult 0).get! ctx.raw).type from rfl] at hInterp'
  dsimp only at hInterp'
  -- The result type is an integer type; extract its width and the poison source value.
  obtain ⟨retTy, hResIntTy⟩ :
      ∃ retTy : IntegerType, ((op.getResult 0).get! ctx.raw).type.val = .integerType retTy := by
    cases hv : ((op.getResult 0).get! ctx.raw).type.val with
    | integerType retTy => exact ⟨retTy, rfl⟩
    | _ => rw [hv] at hInterp'; simp [Interp] at hInterp'
  rw [hResIntTy] at hInterp'
  obtain ⟨rfl, rfl, rfl⟩ :
      resValues = #[RuntimeValue.int retTy.bitwidth
        (Data.LLVM.Int.mlir_poison retTy.bitwidth)] ∧ mem' = state.memory ∧ cf = none := by
    simp only [Interp, pure] at hInterp'
    grind
  have hResVal : newState.variables.getVar? (op.getResult 0)
      = some (.int retTy.bitwidth (Data.LLVM.Int.mlir_poison retTy.bitwidth)) := by
    rw [hNew, VariableState.getVar?_getResult_of_setResultValues? (by rw [hNRes]; omega) hSet]; simp
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hResVal] at hsourceValues
  subst sourceValues
  -- Peel the two created ops: `riscv.li` and the `replaceWithRegLocal` cast-back.
  peelOpCreation hpattern ctx₁ liOp hLi
  rw [WfRewriter.createOp!_none_eq (by clear hpattern; grind) (by clear hpattern; simp)
    (by clear hpattern; simp)] at hLi
  peelOpCreation hpattern ctx₂ castOp hCast
  simp only [replaceWithRegLocal] at hCast
  rw [WfRewriter.createOp!_none_eq (by clear hpattern; grind) (by clear hpattern; simp)
    (by clear hpattern; simp)] at hCast
  cleanupHpattern hpattern
  have hLiType : liOp.getOpType! ctx₂.raw = .riscv .li := by grind
  have hCastType : castOp.getOpType! ctx₂.raw = .builtin .unrealized_conversion_cast := by grind
  have hLiOperands : liOp.getOperands! ctx₂.raw = #[] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hLi (operation := liOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCast (operation := liOp)]
  have hCastOperands : castOp.getOperands! ctx₂.raw = #[ValuePtr.opResult (liOp.getResult 0)] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hCast (operation := castOp)]
  have hLiProps : liOp.getProperties! ctx₂.raw (.riscv .li)
      = { value := IntegerAttr.mk 0 (IntegerType.mk 64) } := by
    grind [OperationPtr.getProperties!_WfRewriter_createOp hLi (operation := liOp),
      OperationPtr.getProperties!_WfRewriter_createOp_ne hCast]
  have hLiResTypes : liOp.getResultTypes! ctx₂.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hLi (operation := liOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCast (operation := liOp)]
  have hCastResTypes : castOp.getResultTypes! ctx₂.raw
      = #[⟨Attribute.integerType retTy, (by grind)⟩] := by
    have hty1 : ((op.getResult 0).get! ctx₁.raw).type = ⟨Attribute.integerType retTy, by grind⟩ := by
      have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₁.raw
          = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
        grind [ValuePtr.getType!_WfRewriter_createOp hLi
          (value := ValuePtr.opResult (op.getResult 0))]
      simp only [ValuePtr.getType!_opResult] at h1
      rw [h1]; exact Subtype.ext hResIntTy
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCast (operation := castOp)]
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
    interpretOp_riscv_li_forward (state := state') (inBounds := by grind)
      hLiType hLiProps hLiOperands hLiResTypes
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
    interpretOp_castBack_forward (state := s₁) (inBounds := by grind)
      hCastType hCastOperands hCastResTypes hRes₁
  refine ⟨s₂, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, liftM, monadLift, MonadLift.monadLift, Interp]
  · refine ⟨#[RuntimeValue.int retTy.bitwidth
        (RISCV.Reg.toInt (Data.RISCV.li (BitVec.ofInt 64 (IntegerAttr.mk 0 (IntegerType.mk 64)).value))
          retTy.bitwidth)], ?_, ?_⟩
    · simp [hRes₂, Option.bind, Option.map]
    · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, by simpa using mlir_poison_isRefinedBy _⟩

end Veir
