import Veir.PatternRewriter.Basic
import Veir.Interpreter.WellFormed
import Veir.IR.WellFormed
import Veir.Rewriter.WellFormed.Builder
import Veir.Rewriter.GetSetInBounds

namespace Veir

def LocalRewritePattern.ReturnOpsWf
  (pattern : LocalRewritePattern OpCode) : Prop :=
  ∀ ctx (op : OperationPtr),
  ∀ newCtx newOps newValues, pattern ctx op = some (newCtx, some (newOps, newValues)) →
  ∀ newOp ∈ newOps, newOp.InBounds newCtx ∧ ¬newOp.InBounds ctx

def LocalRewritePattern.WellFormedContext
  (pattern : LocalRewritePattern OpCode) : Prop :=
  ∀ ctx (op : OperationPtr),
  ctx.WellFormed →
  ∀ newCtx newOps newValues, pattern ctx op = some (newCtx, some (newOps, newValues)) →
  newCtx.WellFormed

def LocalRewritePattern.MatchValues (pattern : LocalRewritePattern OpCode) : Prop :=
  ∀ ctx (op : OperationPtr) (_ : op.InBounds ctx),
  ∀ newCtx newOps newValues, pattern ctx op = some (newCtx, some (newOps, newValues)) →
  newValues.size = op.getNumResults! ctx

def LocalRewritePattern.PreservesSemantics
  (pattern : LocalRewritePattern OpCode)
  (safePattern : pattern.ReturnOpsWf)
  (patternWfCtx : pattern.WellFormedContext)
  (_ : pattern.MatchValues) : Prop :=
  ∀ ctx (ctxWf : ctx.WellFormed) (op : OperationPtr) (opInBounds : op.InBounds ctx),
  ∀ newCtx newOps newValues (hpattern : pattern ctx op = some (newCtx, some (newOps, newValues))),
  ∀ (state : InterpreterState), state.WellFormed ctx →
  ∀ newState cf, interpretOp ctx op state = some (newState, cf) →
  ∃ newState',
    interpretOpList' newCtx newOps.toList state (by grind [ReturnOpsWf]) (by grind [WellFormedContext]) = some (newState', cf) ∧
    ∀ idx (hIdx : idx < newValues.size),
      newState.getVar? (op.getResult idx) = newState'.getVar? newValues[idx]


namespace Example

def matchOp (op : OperationPtr) (ctx : IRContext OpCode) (opType : OpCode) (numOperands : Nat) :
    Option (Array ValuePtr × propertiesOf opType) := do
  guard (op.getOpType! ctx = opType)
  guard (op.getNumOperands! ctx = numOperands)
  guard (op.getNumResults! ctx = 1)
  let operands := op.getOperands! ctx
  some (operands, op.getProperties! ctx opType)

theorem matchOp_implies (opInBounds : op.InBounds ctx) :
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
    interpretOp' opType properties ((op.get! ctx).results.map (·.type)) values = some (#[newValue], cf) ∧
    newState = state.setVar (op.getResult 0) newValue := by
  intro hmatch hinterp
  have ⟨hOpType, hNumOperands, hNumResults, hOperands, hProperties⟩ := matchOp_implies opInBounds hmatch
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
  grind [InterpreterState.setResultValues, InterpreterState.setResultValues_loop]


def matchAddi (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf .arith_addi) := do
  let (op, properties) ← matchOp op ctx .arith_addi 2
  return (op[0]!, op[1]!, properties)

theorem matchAddi_implies (opInBounds : op.InBounds ctx) :
  matchAddi op ctx = some (lhs, rhs, properties) →
  op.getOpType! ctx = .arith_addi ∧
  op.getNumResults! ctx = 1 ∧
  op.getOperands! ctx = #[lhs, rhs] ∧
  properties = op.getProperties! ctx .arith_addi := by
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
    interpretOp' .arith_addi properties #[((op.getResult 0).get! ctx).type] #[lhsVal, rhsVal] = some (#[newValue], cf) ∧
    newState = state.setVar (op.getResult 0) newValue := by
  intro hmatch
  simp only [matchAddi, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq, Prod.mk.injEq, Prod.exists] at hmatch
  have ⟨operands, properties, hmatchOp, hlhs, hrhs, hprop⟩ := hmatch
  have ⟨hOpType, hNumOperands, hNumResults, hOperands, hProperties⟩ := matchOp_implies opInBounds hmatchOp
  intro hinterp
  have ⟨values, newValue, hValues, hinterp', hnewState⟩ := matchOp_interpretOp opInBounds hmatchOp hinterp
  have : operands = #[lhs, rhs] := by grind
  subst this
  simp only [List.mapM_toArray, List.mapM_cons, List.mapM_nil, Option.pure_def, Option.bind_eq_bind,
    Option.bind_some, Option.map_eq_map, Option.map_bind, Option.bind_eq_some_iff,
    Function.comp_apply, Option.some.injEq, Option.map_some] at hValues
  have : #[((op.getResult 0).get! ctx).type] = (op.get! ctx).results.map (·.type) := by sorry
  grind

def matchConstantOp (op : OperationPtr) (ctx : IRContext OpCode) : Option IntegerAttr := do
  let .arith_constant := op.getOpType! ctx | none
  let properties := op.getProperties! ctx .arith_constant
  return properties.value

def matchConstantVal (val : ValuePtr) (ctx : IRContext OpCode) : Option IntegerAttr := do
  let .opResult opResultPtr := val | none
  let op := opResultPtr.op
  matchConstantOp op ctx

theorem matchConstantVal_opRes :
    matchConstantVal val ctx = some cst →
    ∃ op,
      val = .opResult (op.getResult 0) ∧
      matchConstantOp op ctx = some cst := by
  sorry -- Missing lemmas about constant and number of results

theorem matchConstantVal_state_get {state : InterpreterState} :
    matchConstantVal val ctx = some cst →
    state.WellFormed ctx →
    state.getVar? val = some value →
    value = .int cst.type.bitwidth (.val (BitVec.ofNat cst.type.bitwidth cst.value.toNat)) := by
  intro hMatch stateWf stateVar
  have ⟨op, hVal, hConst⟩ := matchConstantVal_opRes hMatch
  subst val
  simp only [InterpreterState.WellFormed] at stateWf
  have eqLemma := stateWf (op.getResult 0) (by sorry) value stateVar
  simp only [InterpreterState.SatisfiesEquationLemma] at eqLemma
  have ⟨cf, hinterp⟩ := eqLemma
  simp [interpretOp] at hinterp
  sorry -- Just have to continue more here

def addIConstantFolding (ctx: IRContext OpCode) (op: OperationPtr) :
    Option (IRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  -- Match an `arith.addi`
  let (lhs, rhs, _) ← matchAddi op ctx
  let lhsConst ← matchConstantVal lhs ctx
  let rhsConst ← matchConstantVal rhs ctx

  -- Sum both constant values
  let newConst := ArithConstantProperties.mk (IntegerAttr.mk ((lhsConst.value + rhsConst.value) % 2 ^ 32) (IntegerType.mk 32))
  let (ctx, newOp) ← Rewriter.createOp ctx .arith_constant #[IntegerType.mk 32] #[] #[] #[] newConst none sorry sorry sorry sorry sorry
  return (ctx, some (#[newOp], #[newOp.getResult 0]))


theorem addIConstantFolding_returnOpsWf :
    LocalRewritePattern.ReturnOpsWf addIConstantFolding := by
  simp only [LocalRewritePattern.ReturnOpsWf, addIConstantFolding]
  intro ctx op newCtx newOps newValues
  simp [Option.bind_eq_some_iff]
  intro lhs rhs _ hMatchAdd lhsConst matchLhs rhsConst matchRhs newCtx' newOp hNewCtx _ _ _ newOp'
  subst newCtx' newOps newValues
  simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false]
  intro _; subst newOp'
  constructor -- Missing InBounds lemmas
  · sorry
  · sorry

theorem addIConstantFolding_wellFormedContext :
    LocalRewritePattern.WellFormedContext addIConstantFolding := by
  simp only [LocalRewritePattern.WellFormedContext, addIConstantFolding]
  intro ctx op ctxWf newCtx newOps
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
    Prod.mk.injEq, Prod.exists, forall_exists_index, and_imp]
  intro newValues lhs rhs _ hMatchAdd lhsConst matchLhs rhsConst matchRhs newCtx' newOp hNewCtx _ _ _
  subst newCtx' newOps newValues
  apply Rewriter.createOp_WellFormed _ hNewCtx
  grind

theorem addIConstantFolding_matchValues :
    LocalRewritePattern.MatchValues addIConstantFolding := by
  simp only [LocalRewritePattern.MatchValues, addIConstantFolding]
  intro ctx op opInBounds newCtx newOps
  simp [Option.bind_eq_some_iff]
  intro newValues lhs rhs _ hMatchAdd lhsConst matchLhs rhsConst matchRhs newCtx' newOp hNewCtx _ _ _
  subst newCtx' newOps newValues
  have := matchAddi_implies (by sorry) hMatchAdd
  grind

theorem addIConstantFolding_preservesSemantics :
    LocalRewritePattern.PreservesSemantics addIConstantFolding addIConstantFolding_returnOpsWf addIConstantFolding_wellFormedContext addIConstantFolding_matchValues := by
  -- Unfold definition and cleanup hypotheses
  simp only [LocalRewritePattern.PreservesSemantics, addIConstantFolding]
  intro ctx ctxWf op opInBounds newCtx newOps newValues hpattern state stateWf newState cf hinterp
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
    Prod.mk.injEq, Prod.exists] at hpattern
  have ⟨lhs, rhs, properties, matchAdd, lhsConst, matchLhs, rhsConst, matchRhs, newCtx', newOp, hNewCtx, _, _, _⟩ := hpattern; clear hpattern
  subst newCtx' newOps newValues

  -- Unfold interpretation of the original add operation parametrized by the lhs and rhs values
  have ⟨hAddOpCode, hOpNumResults, hOpOperands, hOpProperties⟩ := matchAddi_implies opInBounds matchAdd
  have ⟨lhsVal, rhsVal, newValue, hLhsVal, hRhsVal, hInterpOp, hNewState⟩ := matchAddi_interpretOp opInBounds matchAdd hinterp
  subst hNewState
  have lhsValDef := matchConstantVal_state_get matchLhs stateWf hLhsVal
  have rhsValDef := matchConstantVal_state_get matchRhs stateWf hRhsVal
  subst lhsVal rhsVal
  simp only [interpretOp', ne_eq, Option.pure_def, dite_not, Option.dite_none_right_eq_some,
    Option.some.injEq, Prod.mk.injEq, Array.mk.injEq, List.cons.injEq, and_true,
    exists_and_right] at hInterpOp
  have ⟨⟨eqBitwidths, hNewValue⟩, hcf⟩ := hInterpOp; subst cf

  -- Unfold interpretation of new operation
  simp only [List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_one_iff,
    List.getElem_toArray, List.getElem_singleton, forall_eq]
  simp only [InterpreterState.getVar?_setVar, ↓reduceIte]
  simp only [interpretOpList', interpretOp]
  have newOpOperands : state.getOperandValues newCtx newOp = some #[] := by sorry -- Missing lemma
  have newOpType : newOp.getOpType! newCtx = .arith_constant := by sorry -- Missing lemma
  simp only [newOpOperands, Option.pure_def, Option.bind_eq_bind, Option.bind_some]
  simp [interpretOp']; rw [newOpType]
  simp only
  have ⟨res0, hres0⟩ : ∃ opr, (newOp.get! newCtx).results[0]? = some opr := by sorry -- Missing lemmas
  have : res0.type.val = .integerType (IntegerType.mk 32) := by sorry -- Missing lemma about createOp and result types
  simp only [hres0, Option.map_some, Option.bind_some, this, Option.some.injEq, Prod.mk.injEq,
    and_true, exists_eq_left']
  have : newOp.getNumResults! newCtx = 1 := by sorry -- Missing lemma
  simp only [InterpreterState.setResultValues, this, InterpreterState.setResultValues_loop,
    List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_add_one,
    getElem!_pos, List.getElem_toArray, List.getElem_cons_zero]

  -- actual proof of the rewrite
  subst newValue
  simp only [InterpreterState.getVar?_setVar, ↓reduceIte, Option.some.injEq,
    RuntimeValue.int.injEq]
  have lhsBitwidth : lhsConst.type.bitwidth = 32 := by sorry -- TODO
  simp only [lhsBitwidth, true_and]
  have : (newOp.getProperties! newCtx .arith_constant) = { value := { value := (lhsConst.value + rhsConst.value) % 2 ^ 32, type := { bitwidth := 32 } } } := by sorry
  simp only [this]
  rw [HAdd.hAdd, instHAdd]
  simp only [Add.add, Data.LLVM.Int.add, Data.LLVM.Int.cast, BitVec.cast_ofNat]
  rw [lhsBitwidth]
  congr
  sorry
