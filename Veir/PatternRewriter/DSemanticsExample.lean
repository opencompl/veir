import Veir.PatternRewriter.Basic
import Veir.DInterpreter
import Veir.IR.WellFormed
import Veir.Passes.Matching
import Veir.Rewriter.WfRewriter
import Veir.PatternRewriter.DSemantics
import Veir.Data.LLVM.Int.Basic

open Veir.Data

namespace Veir
namespace Example

variable {OpInfo : Type} [HasOpInfo OpInfo] {ctx : WfIRContext OpCode}

theorem matchOp_implies :
  matchOp op ctx.raw opType numOperands = some (operands, properties) →
  op.getOpType! ctx.raw = opType ∧
  op.getNumOperands! ctx.raw = numOperands ∧
  op.getNumResults! ctx.raw = 1 ∧
  operands = op.getOperands! ctx.raw ∧
  properties = op.getProperties! ctx opType := by
  simp only [matchOp]
  simp only [guard, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, ite_eq_left_iff,
    reduceCtorEq, imp_false, Decidable.not_not, Option.some.injEq, Prod.mk.injEq, exists_const,
    and_imp]
  intros
  grind

def matchAddi (op : OperationPtr) (ctx : WfIRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.arith .addi)) := do
  let (op, properties) ← matchOp op ctx (.arith .addi) 2
  return (op[0]!, op[1]!, properties)

theorem matchAddi_implies :
  matchAddi op ctx = some (lhs, rhs, properties) →
  op.getOpType! ctx.raw = .arith .addi ∧
  op.getNumResults! ctx.raw = 1 ∧
  op.getOperands! ctx.raw = #[lhs, rhs] ∧
  properties = op.getProperties! ctx.raw (.arith .addi) := by
  intro hmatch
  simp only [matchAddi, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq, Prod.mk.injEq, Prod.exists] at hmatch
  grind [matchOp_implies]

theorem matchAddi_interpretOp_unfold (opInBounds : op.InBounds ctx.raw) :
    matchAddi op ctx = some (lhs, rhs, properties) →
    interpretOp ctx op state = (newState, cf) →
    let intType := arithAddi_getType ctx op (by sorry)
    let lhsVal := state.getVar'! lhs (LLVM.Int intType.bitwidth) (by sorry)
    let rhsVal := state.getVar'! rhs (LLVM.Int intType.bitwidth) (by sorry)
    newState.getVar'! (op.getResult 0) (LLVM.Int intType.bitwidth) (by sorry) =
    (lhsVal.add rhsVal properties.nsw properties.nuw) ∧ cf = none := by
  sorry

def matchConstantOp (op : OperationPtr) (ctx : IRContext OpCode) : Option IntegerAttr := do
  let .arith .constant := op.getOpType! ctx | none
  let properties := op.getProperties! ctx (.arith .constant)
  return properties.value

theorem matchConstantOp_implies :
    matchConstantOp op ctx.raw = some properties →
    op.getOpType! ctx.raw = .arith .constant ∧
    op.getNumResults! ctx.raw = 1 ∧
    op.getOperands! ctx.raw = #[] ∧
    properties = (op.getProperties! ctx.raw (.arith .constant)).value := by
  sorry

theorem matchConstantOp_interpretOp_unfold (opInBounds : op.InBounds ctx.raw) :
    matchConstantOp op ctx = some properties →
    interpretOp ctx op state = (newState, cf) →
    newState.getVar'! (op.getResult 0) (LLVM.Int (arithConstant_getType ctx op (by sorry)).bitwidth) =
    LLVM.Int.val (BitVec.ofInt (arithConstant_getType ctx op (by sorry)).bitwidth properties.value) := by
  sorry

def addIConstantFolding (ctx: WfIRContext OpCode) (op: OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  -- Match an `arith.addi`
  let (lhs, rhs, addProp) ← matchAddi op ctx
  if addProp.nsw || addProp.nuw then
    return (ctx, none)
  let lhsOp ← lhs.getDefiningOp! ctx.raw
  let rhsOp ← rhs.getDefiningOp! ctx.raw
  let lhsConst ← matchConstantOp lhsOp ctx
  let rhsConst ← matchConstantOp rhsOp ctx

  -- Sum both constant values
  let .integerType intType := (lhs.getType! ctx.raw).val | none
  let newConst := ArithConstantProperties.mk (IntegerAttr.mk ((BitVec.ofInt intType.bitwidth lhsConst.value) + (BitVec.ofInt intType.bitwidth rhsConst.value)).toInt intType)
  let (ctx, newOp) ← WfRewriter.createOp ctx (.arith .constant) #[intType] #[] #[] #[] newConst none sorry sorry sorry sorry
  return (ctx, some (#[newOp], #[newOp.getResult 0]))

theorem ValuePtr.getDefiningOp!.numResults_zero {ctx : IRContext OpInfo} {op : OperationPtr} {value : ValuePtr} :
    value.getDefiningOp! ctx = op →
    op.getNumResults! ctx = 1 →
    value = op.getResult 0 := by
  sorry

grind_pattern ValuePtr.getDefiningOp!.numResults_zero =>
    value.getDefiningOp! ctx, op.getNumResults! ctx

set_option maxHeartbeats 100000000 in
theorem addIConstantFolding_preservesSemantics :
    LocalRewritePattern.PreservesSemantics addIConstantFolding h hVal hTypes := by
  -- Unfold definition and cleanup hypotheses
  simp only [LocalRewritePattern.PreservesSemantics, addIConstantFolding]
  intro ctx ctxDom op opInBounds newCtx newOps newValues hpattern state stateWf newState cf hinterp
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
    Prod.mk.injEq, Prod.exists] at hpattern
  have ⟨lhs, rhs, properties, matchAdd, hpattern₂⟩ := hpattern
  split at hpattern₂; grind; rename_i hProperties; clear hpattern
  simp [Option.bind_eq_some_iff] at hpattern₂
  have ⟨lhsOp, hLhsOp, rhsOp, hRhsOp, lhsConst, matchLhs, rhsConst, matchRhs, hpattern₃⟩ := hpattern₂; clear hpattern₂
  split at hpattern₃; rotate_left; grind; rename_i intType hIntType
  simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq, Prod.exists] at hpattern₃
  have ⟨newCtx', newOp, hNewCtx, _, _, _⟩ := hpattern₃; clear hpattern₃
  subst newCtx' newOps newValues

  -- Add some useful information from the matches
  have := matchConstantOp_implies matchLhs
  have := matchConstantOp_implies matchRhs
  have := matchAddi_implies matchAdd

  have : lhs.InBounds ctx.raw := by grind [OperationPtr.getOperands!_inBounds]
  have : rhs.InBounds ctx.raw := by grind [OperationPtr.getOperands!_inBounds]

  -- Unfold interpretation of the original add operation
  have ⟨hRes, _⟩ := matchAddi_interpretOp_unfold (by grind) matchAdd hinterp
  clear hinterp; subst cf

  -- Introduce equation lemma for `lhs`, and unfold the interpretation of it
  have ⟨cfLhs, hInterpLhs⟩ := stateWf lhsOp (by grind) (by grind)
  have hLhsRes := matchConstantOp_interpretOp_unfold (by grind) matchLhs hInterpLhs
  clear hInterpLhs

  -- Introduce equation lemma for `rhs`, and unfold the interpretation of it
  have ⟨cfRhs, hInterpRhs⟩ := stateWf rhsOp (by grind) (by grind)
  have hRhsRes := matchConstantOp_interpretOp_unfold (by grind) matchRhs hInterpRhs
  clear hInterpRhs

  -- Substitute lhs and rhs values
  have : lhs = ValuePtr.opResult (lhsOp.getResult 0) := by grind
  have : rhs = ValuePtr.opResult (rhsOp.getResult 0) := by grind
  subst lhs rhs

  -- Unfold interpretation of new operation
  simp only [interpretOpList']
  generalize hInterpNew : (interpretOp newCtx newOp (state.move newCtx)) = interpNewOp
  simp only [interpretOp] at hInterpNew
  have hInterpConstant : interpNewOp = (interpretConstant newCtx newOp (state.move newCtx) (by grind), none) := by grind
  clear hInterpNew
  simp [interpretConstant] at hInterpConstant
  subst interpNewOp
  simp only [Prod.mk.injEq, and_true, List.size_toArray, List.length_cons, List.length_nil,
    Nat.zero_add, Nat.lt_one_iff, List.getElem_toArray, exists_eq_left']
  intro idx hIdx; subst idx
  simp only [List.getElem_cons_zero]
  simp only [InterpreterState.getVar!_setVar', ↓reduceDIte]
  simp only [InterpreterState.getVar'!_eq_getVar!]
  simp only [InterpreterState.getVar'!_of_getVar'! hRes]
  simp only [InterpreterState.getVar'!_of_getVar'! hLhsRes]
  simp only [InterpreterState.getVar'!_of_getVar'! hRhsRes]

  have : newOp.getProperties! newCtx.raw (.arith .constant) = { value := { value := (lhsConst.value + rhsConst.value).bmod (2 ^ intType.bitwidth), type := intType } } := by sorry
  simp only [this]
  rw [toto (h' := sorry /- Should be derivable.-/)]
  rw [toto (h' := sorry /- Should be derivable.-/)]
  -- works:
  simp
  have heq w k₁ k₂ nsw nuw :
    (LLVM.Int.val (BitVec.ofInt w k₁)).add (LLVM.Int.val (BitVec.ofInt w k₂)) nsw nuw =
    LLVM.Int.val (BitVec.ofInt w ((k₁ + k₂).bmod (2 ^ w))) := sorry
  grind



theorem addIConstantFolding_preservesSemantics_alternative :
    LocalRewritePattern.PreservesSemantics addIConstantFolding h hVal hTypes := by
  -- Unfold definition and cleanup hypotheses
  simp only [LocalRewritePattern.PreservesSemantics, addIConstantFolding]
  intro ctx ctxDom op opInBounds newCtx newOps newValues hpattern state stateWf newState cf hinterp
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
    Prod.mk.injEq, Prod.exists] at hpattern
  have ⟨lhs, rhs, properties, matchAdd, hpattern₂⟩ := hpattern
  split at hpattern₂; grind; rename_i hProperties; clear hpattern
  simp [Option.bind_eq_some_iff] at hpattern₂
  have ⟨lhsOp, hLhsOp, rhsOp, hRhsOp, lhsConst, matchLhs, rhsConst, matchRhs, hpattern₃⟩ := hpattern₂; clear hpattern₂
  split at hpattern₃; rotate_left; grind; rename_i intType hIntType
  simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq, Prod.exists] at hpattern₃
  have ⟨newCtx', newOp, hNewCtx, _, _, _⟩ := hpattern₃; clear hpattern₃
  subst newCtx' newOps newValues

  -- Add some useful information from the matches
  have := matchConstantOp_implies matchLhs
  have := matchConstantOp_implies matchRhs
  have := matchAddi_implies matchAdd

  have : lhs.InBounds ctx.raw := by grind [OperationPtr.getOperands!_inBounds]
  have : rhs.InBounds ctx.raw := by grind [OperationPtr.getOperands!_inBounds]

  have : lhs = ValuePtr.opResult (lhsOp.getResult 0) := by grind
  have : rhs = ValuePtr.opResult (rhsOp.getResult 0) := by grind
  subst lhs rhs

  -- Start unfolding interpretation of new operation
  simp only [interpretOpList']
  generalize hInterpNew : (interpretOp newCtx newOp (state.move newCtx)) = interpNewOp
  simp only [interpretOp] at hInterpNew
  have hInterpConstant : interpNewOp = (interpretConstant newCtx newOp (state.move newCtx) (by grind), none) := by grind
  clear hInterpNew
  simp [interpretConstant] at hInterpConstant
  subst interpNewOp
  simp only [Prod.mk.injEq, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add,
    Nat.lt_one_iff, List.getElem_toArray]

  -- Take care of `cf` proof, should find a way to make this better
  refine ⟨_, ⟨rfl, (matchAddi_interpretOp_unfold (by grind) matchAdd hinterp).2.symm⟩, ?_⟩
  intro idx hIdx; subst idx

  -- Interpret new operation
  simp only [List.getElem_cons_zero]
  simp only [InterpreterState.getVar!_setVar', ↓reduceDIte]
  have : newOp.getProperties! newCtx.raw (.arith .constant) = { value := { value := (lhsConst.value + rhsConst.value).bmod (2 ^ intType.bitwidth), type := intType } } := by sorry
  simp only [this]

  -- Setup interpretation of the original root
  simp only [InterpreterState.getVar'!_eq_getVar!]

  -- Unfold interpretation of the original add operation
  have ⟨hRes, _⟩ := matchAddi_interpretOp_unfold (by grind) matchAdd hinterp
  clear hinterp; subst cf
  simp only [InterpreterState.getVar'!_of_getVar'! hRes]; clear hRes

  -- Introduce equation lemma for `lhs`, and unfold the interpretation of it
  have ⟨cfLhs, hInterpLhs⟩ := stateWf lhsOp (by grind) (by grind)
  have hLhsRes := matchConstantOp_interpretOp_unfold (by grind) matchLhs hInterpLhs
  clear hInterpLhs
  simp only [InterpreterState.getVar'!_of_getVar'! hLhsRes]; clear hLhsRes

  -- Introduce equation lemma for `rhs`, and unfold the interpretation of it
  have ⟨cfRhs, hInterpRhs⟩ := stateWf rhsOp (by grind) (by grind)
  have hRhsRes := matchConstantOp_interpretOp_unfold (by grind) matchRhs hInterpRhs
  clear hInterpRhs
  simp only [InterpreterState.getVar'!_of_getVar'! hRhsRes]; clear hRhsRes

  -- Now this is the actual proof


  sorry
