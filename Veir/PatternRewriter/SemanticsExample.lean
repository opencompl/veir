import Veir.PatternRewriter.Basic
import Veir.Interpreter
import Veir.IR.WellFormed
import Veir.Passes.Matching
import Veir.Rewriter.WfRewriter
import Veir.PatternRewriter.Semantics
import Veir.Verifier

namespace Veir
namespace Example

variable {OpInfo : Type} [HasOpInfo OpInfo]

theorem matchOp_implies :
  matchOp op ctx opType numOperands = some (operands, properties) →
  op.getOpType! ctx = opType ∧
  op.getNumOperands! ctx = numOperands ∧
  op.getNumResults! ctx = 1 ∧
  operands = op.getOperands! ctx ∧
  properties = op.getProperties! ctx opType := by
  simp only [matchOp]
  simp only [guard, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, ite_eq_left_iff,
    reduceCtorEq, imp_false, Decidable.not_not, Option.some.injEq, Prod.mk.injEq, exists_const,
    and_imp]
  intros
  grind

theorem matchOp_interpretOp
  (opInBounds : op.InBounds ctx) :
  matchOp op ctx opType numOperands = some (operands, properties) →
  interpretOp ctx op state = some (newState, cf) →
  ∃ values newValue,
    operands.mapM state.getVar? = some values ∧
    interpretOp' opType properties (op.getResultTypes! ctx) values (op.getSuccessors! ctx) = some (#[newValue], cf) ∧
    newState = state.setVar (op.getResult 0) newValue := by
  intro hmatch hinterp
  have ⟨hOpType, hNumOperands, hNumResults, hOperands, hProperties⟩ := matchOp_implies hmatch
  simp only [interpretOp] at hinterp
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
    Prod.mk.injEq, Prod.exists, exists_eq_right_right] at hinterp
  have ⟨values, hValues, resValues, hInterpOp', hNewState⟩ := hinterp; clear hinterp
  exists values
  subst operands
  simp [InterpreterState.getOperandValues] at hValues
  simp only [hValues, true_and]
  have : resValues.size = 1 := by sorry -- Missing lemma about number of results and interpretation
  exists resValues[0]
  have : resValues = #[resValues[0]] := by grind
  constructor
  · grind
  · grind [InterpreterState.setResultValues, InterpreterState.setResultValues_loop]

theorem matchOp_interpretOp'
  (opInBounds : op.InBounds ctx) :
  matchOp op ctx opType numOperands = some (operands, properties) →
  interpretOp ctx op state = some (newState, cf) →
  ∃ values newValue,
    operands.mapM state.getVar? = some values ∧
    newState.getVar? (op.getResult 0) = some newValue ∧
    interpretOp' opType properties (op.getResultTypes! ctx) values (op.getSuccessors! ctx) = some (#[newValue], cf) := by
  grind [matchOp_interpretOp]

def matchAddi (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.arith .addi)) := do
  let (op, properties) ← matchOp op ctx (.arith .addi) 2
  return (op[0]!, op[1]!, properties)

theorem matchAddi_implies :
  matchAddi op ctx = some (lhs, rhs, properties) →
  op.getOpType! ctx = .arith .addi ∧
  op.getNumResults! ctx = 1 ∧
  op.getOperands! ctx = #[lhs, rhs] ∧
  properties = op.getProperties! ctx (.arith .addi) := by
  intro hmatch
  simp only [matchAddi, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq, Prod.mk.injEq, Prod.exists] at hmatch
  grind [matchOp_implies]

theorem matchAddi_interpretOp
  (opInBounds : op.InBounds ctx) :
  matchAddi op ctx = some (lhs, rhs, properties) →
  interpretOp ctx op state = some (newState, cf) →
  ∃ lhsVal rhsVal newValue,
    state.getVar? lhs = some lhsVal ∧
    state.getVar? rhs = some rhsVal ∧
    interpretOp' (.arith .addi) properties (op.getResultTypes! ctx) #[lhsVal, rhsVal] #[] = some (#[newValue], cf) ∧
    newState = state.setVar (op.getResult 0) newValue := by
  intro hmatch
  simp only [matchAddi, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq, Prod.mk.injEq, Prod.exists] at hmatch
  have ⟨operands, properties, hmatchOp, hlhs, hrhs, hprop⟩ := hmatch
  have ⟨hOpType, hNumOperands, hNumResults, hOperands, hProperties⟩ := matchOp_implies hmatchOp
  intro hinterp
  have ⟨values, newValue, hValues, hinterp', hnewState⟩ := matchOp_interpretOp opInBounds hmatchOp hinterp
  have : operands = #[lhs, rhs] := by grind
  subst this
  simp only [List.mapM_toArray, List.mapM_cons, List.mapM_nil, Option.pure_def, Option.bind_eq_bind,
    Option.bind_some, Option.map_eq_map, Option.map_bind, Option.bind_eq_some_iff,
    Function.comp_apply, Option.some.injEq, Option.map_some] at hValues
  have : (op.getResultTypes! ctx) = #[((op.getResult 0).get! ctx).type] := by grind
  have : (op.getSuccessors! ctx) = #[] := by sorry
  grind

theorem matchAddi_interpretOp'
  (opInBounds : op.InBounds ctx) :
  matchAddi op ctx = some (lhs, rhs, properties) →
  interpretOp ctx op state = some (newState, cf) →
  ∃ lhsVal rhsVal newValue,
    state.getVar? lhs = some lhsVal ∧
    state.getVar? rhs = some rhsVal ∧
    newState.getVar? (op.getResult 0) = some newValue ∧
    interpretOp' (.arith .addi) properties #[((op.getResult 0).get! ctx).type] #[lhsVal, rhsVal] #[] = some (#[newValue], cf) := by
  sorry

theorem interpretOp'_arith_addi_eq_some_implies :
    interpretOp' (OpCode.arith Arith.addi) properties #[resType] #[lhsVal, rhsVal] #[] = some (#[res], cf) →
    ∃ bw intLhs intRhs,
    lhsVal = .int bw intLhs ∧
    rhsVal = .int bw intRhs ∧
    res = .int bw (intLhs.add intRhs properties.nsw properties.nuw) ∧
    cf = none := by
  intro h
  --simp only [interpretOp', ne_eq, Option.pure_def, dite_not] at h
  --split at h; rotate_left; grind; rename_i _ bwLhs intLhsVal bwRhs intRhsVal hTemp
  --simp only [List.cons.injEq, and_true] at hTemp; have ⟨_,_⟩ := hTemp; clear hTemp; subst lhsVal rhsVal
  --split at h; rotate_left; grind; subst bwRhs
  --simp at h; have ⟨_, _⟩ := h; clear h; subst cf res
  sorry
  -- simp only [Data.LLVM.Int.cast, BitVec.cast_eq]
  -- exists bwLhs, intLhsVal, intRhsVal
  -- grind

theorem matchAddi_interpretOp_unfold (opInBounds : op.InBounds ctx) :
    matchAddi op ctx = some (lhs, rhs, properties) →
    interpretOp ctx op state = some (newState, cf) →
    ∃ bw intLhs intRhs,
    state.getVar? lhs = some (RuntimeValue.int bw intLhs) ∧
    state.getVar? rhs = some (RuntimeValue.int bw intRhs) ∧
    newState.getVar? (op.getResult 0) = some (RuntimeValue.int bw (intLhs.add intRhs properties.nsw properties.nuw)) ∧
    cf = none := by
  grind [matchAddi_interpretOp', interpretOp'_arith_addi_eq_some_implies]

def matchConstantOp (op : OperationPtr) (ctx : IRContext OpCode) : Option IntegerAttr := do
  let .arith .constant := op.getOpType! ctx | none
  let properties := op.getProperties! ctx (.arith .constant)
  return properties.value

theorem matchConstantOp_implies :
    matchConstantOp op ctx = some properties →
    op.getOpType! ctx = .arith .constant ∧
    op.getNumResults! ctx = 1 ∧
    op.getOperands! ctx = #[] ∧
    properties = (op.getProperties! ctx (.arith .constant)).value := by
  sorry

theorem matchConstantOp_interpretOp'
    (opInBounds : op.InBounds ctx) :
    matchConstantOp op ctx = some (properties) →
    interpretOp ctx op state = some (newState, cf) →
    ∃ newValue,
      newState.getVar? (op.getResult 0) = some newValue ∧
      interpretOp' (.arith .constant) (ArithConstantProperties.mk properties) #[((op.getResult 0).get! ctx).type] #[] #[] = some (#[newValue], cf) := by
  sorry

theorem interpretOp'_arith_constant_eq_some_implies :
    interpretOp' (OpCode.arith Arith.constant) properties #[resType] #[] #[] = some (#[res], cf) →
    ∃ intType,
    resType = Attribute.integerType intType ∧
    res = RuntimeValue.int intType.bitwidth (Data.LLVM.Int.val (BitVec.ofInt intType.bitwidth properties.value.value)) ∧
    cf = none := by
  unfold interpretOp'
  simp only
  grind

theorem matchConstantOp_interpretOp_unfold (opInBounds : op.InBounds ctx) :
    matchConstantOp op ctx = some properties →
    interpretOp ctx op state = some (newState, cf) →
    ((op.getResult 0).get! ctx).type = Attribute.integerType properties.type ∧
    newState.getVar? (op.getResult 0) = some (RuntimeValue.int properties.type.bitwidth (Data.LLVM.Int.val (BitVec.ofInt properties.type.bitwidth properties.value))) ∧
    cf = none := by
  sorry
  --grind [matchConstantOp_interpretOp', interpretOp'_arith_constant_eq_some_implies]


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

theorem addIConstantFolding_preservesSemantics :
    LocalRewritePattern.PreservesSemantics addIConstantFolding h := by
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

  have : lhsOp.Verified ctx := by sorry
  have := OperationPtr.Verified.arith_constant this
  have : rhsOp.Verified ctx := by sorry
  have := OperationPtr.Verified.arith_constant this
  have : op.Verified ctx := by sorry
  have ⟨_, _, _, _, intType', _⟩ := OperationPtr.Verified.arith_addi this (by grind)

  have : lhs = ValuePtr.opResult (lhsOp.getResult 0) := by grind
  have : rhs = ValuePtr.opResult (rhsOp.getResult 0) := by grind
  subst lhs rhs

  -- Unfold interpretation of the original add operation
  have ⟨bw, intLhs, intRhs, hIntLhs, hIntRhs, hAddRes, hCf⟩ := matchAddi_interpretOp_unfold (by grind) matchAdd hinterp
  subst cf; clear hinterp

  -- Introduce equation lemma for `lhs`, and unfold the interpretation of it
  have ⟨cfLhs, hInterpLhs⟩ := stateWf lhsOp (by grind) (by grind)
  have ⟨hLhsResType, hLhsRes, hCf⟩ := matchConstantOp_interpretOp_unfold (by grind) matchLhs hInterpLhs

  -- Introduce equation lemma for `rhs`, and unfold the interpretation of it
  have ⟨cfRhs, hInterpRhs⟩ := stateWf rhsOp (by grind) (by grind)
  have ⟨hRhsResType, hRhsRes, hCf⟩ := matchConstantOp_interpretOp_unfold (by grind) matchRhs hInterpRhs

  -- Resolve the new state values
  simp only [List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_one_iff,
    List.getElem_toArray, List.getElem_singleton, forall_eq, hAddRes]

  simp only [interpretOpList', interpretOp, InterpreterState.getOperandValues]
  simp_getset
  simp only [↓reduceIte, List.mapM_toArray, List.mapM_nil, Option.pure_def, Option.map_eq_map,
    Option.map_some, Option.bind_eq_bind, Option.bind_some]

  have newOpType : newOp.getOpType! newCtx.raw = .arith .constant := by grind
  rw [newOpType]
  simp only [OperationPtr.getProperties!_WfRewriter_createOp hNewCtx, ↓reduceIte]

  -- unfolding interpretOp'
  unfold interpretOp'
  simp only
  unfold Arith.interpretOp'
  simp only [List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add,
    Nat.lt_add_one, getElem?_pos, List.getElem_toArray, List.getElem_cons_zero, Option.pure_def,
    Option.bind_eq_bind, Option.bind_some]
  simp only [Option.some.injEq, Prod.mk.injEq, and_true]
  simp only [InterpreterState.setResultValues]
  simp only [show newOp.getNumResults! newCtx.raw = 1 by grind]
  simp only [InterpreterState.setResultValues_loop, List.size_toArray, List.length_cons,
    List.length_nil, Nat.zero_add, Nat.lt_add_one, getElem!_pos, List.getElem_toArray,
    List.getElem_cons_zero]
  simp only [exists_eq_left']
  simp only [InterpreterState.getVar?_setVar, ↓reduceIte, Option.some.injEq, RuntimeValue.int.injEq]
  have : bw = intType.bitwidth := by grind
  subst bw
  simp only [heq_eq_eq, true_and]

  -- Actual proof
  have hnsw : properties.nsw = false := by grind
  have hnuw : properties.nuw = false := by grind
  simp only [Data.LLVM.Int.add, hnsw, Bool.false_eq_true, false_and, ↓reduceIte, hnuw, pure_bind]
  simp only [Id.run]
  rcases intType with ⟨bw₂⟩
  have : bw₂ = lhsConst.type.bitwidth := by grind
  subst bw₂
  simp only

  simp only [hRhsRes, Option.some.injEq, RuntimeValue.int.injEq] at hIntRhs
  simp only [hLhsRes, Option.some.injEq, RuntimeValue.int.injEq, heq_eq_eq, true_and] at hIntLhs
  subst intLhs
  simp at intRhs
  rcases rhsConst with ⟨rhsConstVal, rhsConstType⟩; rcases lhsConst with ⟨lhsConstVal, lhsConstType⟩
  have : rhsConstType.bitwidth = lhsConstType.bitwidth := by grind
  have : rhsConstType = lhsConstType := by sorry
  subst rhsConstType
  simp at hIntRhs
  subst intRhs
  simp_all
  simp [←BitVec.toInt_inj]
  have : (rhsOp.getProperties! ctx.raw (OpCode.arith Arith.constant)).value.type.bitwidth = lhsConstType.bitwidth := by grind
  simp [this]
