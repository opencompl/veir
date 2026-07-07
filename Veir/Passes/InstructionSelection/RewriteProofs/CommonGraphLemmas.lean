import Veir.PatternRewriter.Basic
import Veir.Interpreter
import Veir.IR.WellFormed
import Veir.Passes.Matching
import Veir.PatternRewriter.Semantics
import Veir.Verifier
import Veir.Dominance
import Veir.Passes.InstructionSelection.RewriteProofs.CommonBaseLemmas

/-!
# Semantic facts about matched subgraphs

A `PreservesSemantics` proof receives a source state satisfying `EquationLemmaAt` at the match
point: every *pure* operation dominating that point has already been interpreted consistently
into the state. The lemmas in this file exploit that invariant to recover the *runtime* values
of operands that a pattern matched only *syntactically* through their defining operations
(`matchNot`, `matchConstantIntVal`, …). This is the extra ingredient that multi-op (DAG)
matching patterns need over the single-op lowerings.

The file provides three layers:
- `OperationPtr.Pure.*`: per-opcode purity facts (required to invoke `EquationLemmaAt`);
- `*_interpretOp_unfold`: unfold one successful `interpretOp` of a given shape into its result
  bindings (usable both for the matched op itself and, at `newState := state`, for the
  `EquationHolds` fact of a matched defining op);
- `matchNot_getVar?_of_EquationLemmaAt`: the packaged graph lemma for `matchNot`.
-/

namespace Veir

/-! ## Purity of the matched defining ops -/

/-- `llvm.xor` is pure: its interpretation neither reads nor writes memory. -/
theorem OperationPtr.Pure.llvm_xor {op : OperationPtr} {ctx : IRContext OpCode}
    (hType : op.getOpType! ctx = .llvm .xor) : op.Pure ctx := by
  unfold OperationPtr.Pure
  rw [hType]
  intro operands memory₁ memory₂
  simp only [interpretOp', Llvm.interpretOp']
  split
  · split <;> simp [Interp.map, Option.map, UBOr.map, pure]
  · simp [Interp.map, Option.map]

/-- `llvm.mlir.constant` is pure: its interpretation neither reads nor writes memory. -/
theorem OperationPtr.Pure.llvm_mlir__constant {op : OperationPtr} {ctx : IRContext OpCode}
    (hType : op.getOpType! ctx = .llvm .mlir__constant) : op.Pure ctx := by
  unfold OperationPtr.Pure
  rw [hType]
  intro operands memory₁ memory₂
  simp only [interpretOp', Llvm.interpretOp']
  repeat' split
  all_goals first
    | rfl
    | simp [Interp.map, Option.map, UBOr.map, pure, bind, Option.bind]

/-! ## Forward unfolding of one interpretation step -/

/-- Interpreting a matched two-operand LLVM op (of opcode `srcOp`, interpreted by `srcFn` per
    `hSemSrc`) whose operands both have integer type `intType` reads the operands' `i{bw}`
    values `x`/`y` and stores `srcFn x y props` in the result variable, leaving memory and
    control flow untouched. The operand values are derived internally (from the successful
    interpretation and the operand types), so they are exposed as existential outputs rather
    than required as inputs. The binop analogue of `matchUnaryOp_interpretOp_unfold`. -/
theorem matchBinaryOp_interpretOp_unfold {srcOp : Llvm} {ctx : WfIRContext OpCode}
    {op : OperationPtr} {lhs rhs : ValuePtr} {props : propertiesOf (.llvm srcOp)} {intType}
    {srcFn : ∀ {bw : Nat},
      Data.LLVM.Int bw → Data.LLVM.Int bw → propertiesOf (.llvm srcOp) → Data.LLVM.Int bw}
    {state newState : InterpreterState ctx} {cf} (opInBounds : op.InBounds ctx.raw)
    (hOpType : op.getOpType! ctx.raw = .llvm srcOp)
    (hNumResults : op.getNumResults! ctx.raw = 1)
    (hOperands : op.getOperands! ctx.raw = #[lhs, rhs])
    (hProps : props = op.getProperties! ctx.raw (.llvm srcOp))
    (hSemSrc : ∀ (bw : Nat) (x y : Data.LLVM.Int bw) (props : propertiesOf (.llvm srcOp))
        (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr) (mem : MemoryState),
        Llvm.interpretOp' srcOp props resultTypes #[.int bw x, .int bw y] blockOperands mem
          = some (.ok (#[.int bw (srcFn x y props)], mem, none)))
    (hinterp : interpretOp op state opInBounds = some (.ok (newState, cf)))
    (hLhsType : (lhs.getType! ctx.raw).val = Attribute.integerType intType)
    (hRhsType : (rhs.getType! ctx.raw).val = Attribute.integerType intType) :
    ∃ x y, state.variables.getVar? lhs = some (RuntimeValue.int intType.bitwidth x) ∧
      state.variables.getVar? rhs = some (RuntimeValue.int intType.bitwidth y) ∧
      state.memory = newState.memory ∧
      newState.variables.getVar? (op.getResult 0) =
        some (RuntimeValue.int intType.bitwidth (srcFn x y props)) ∧
      cf = none := by
  have hNumOperands : op.getNumOperands! ctx.raw = 2 := by
    simp [← OperationPtr.getOperands!.size_eq_getNumOperands!, hOperands]
  have hLhsEq : lhs = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hRhsEq : rhs = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  -- Derive the operands' `i{bw}` values from the successful interpretation and their types.
  obtain ⟨operandValues, _, _, _, hOperandValues, _⟩ := interpretOp_some_iff.mp hinterp
  simp only [VariableState.getOperandValues] at hOperandValues
  have hsize0 : 0 < (op.getOperands! ctx.raw).size := by
    rw [OperationPtr.getOperands!.size_eq_getNumOperands!]; omega
  have hsize1 : 1 < (op.getOperands! ctx.raw).size := by
    rw [OperationPtr.getOperands!.size_eq_getNumOperands!]; omega
  obtain ⟨lval, hlval⟩ :=
    Array.exists_mapM_option_eq_some_iff.mp ⟨operandValues, hOperandValues⟩ 0 hsize0
  obtain ⟨rval, hrval⟩ :=
    Array.exists_mapM_option_eq_some_iff.mp ⟨operandValues, hOperandValues⟩ 1 hsize1
  have hlGetVar : state.variables.getVar? lhs = some lval := by
    rw [hLhsEq, show (op.getOperands! ctx.raw)[0]! = (op.getOperands! ctx.raw)[0] from by grind]
    exact hlval
  have hrGetVar : state.variables.getVar? rhs = some rval := by
    rw [hRhsEq, show (op.getOperands! ctx.raw)[1]! = (op.getOperands! ctx.raw)[1] from by grind]
    exact hrval
  have hlconf := VariableState.getVar?_conforms hlGetVar
  rw [show lhs.getType! ctx.raw = ⟨.integerType intType, hLhsType ▸ (lhs.getType! ctx.raw).2⟩
        from Subtype.ext hLhsType] at hlconf
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType hlconf
  have hrconf := VariableState.getVar?_conforms hrGetVar
  rw [show rhs.getType! ctx.raw = ⟨.integerType intType, hRhsType ▸ (rhs.getType! ctx.raw).2⟩
        from Subtype.ext hRhsType] at hrconf
  obtain ⟨y, rfl⟩ := RuntimeValue.Conforms.integerType hrconf
  refine ⟨x, y, hlGetVar, hrGetVar, ?_⟩
  -- With the values in hand, unfold the interpretation of the matched op.
  have hOperand0 : op.getOperand! ctx.raw 0 = lhs := by
    rw [hLhsEq]
    grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = rhs := by
    rw [hRhsEq]
    grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOpVals : state.variables.getOperandValues op
      = some #[RuntimeValue.int intType.bitwidth x, RuntimeValue.int intType.bitwidth y] := by
    rw [VariableState.getOperandValues_eq_some_iff]
    refine ⟨by simp [hNumOperands], fun i hi => ?_⟩
    rw [hNumOperands] at hi
    match i, hi with
    | 0, _ => simpa [hOperand0] using hlGetVar
    | 1, _ => simpa [hOperand1] using hrGetVar
  rw [interpretOp_some_iff] at hinterp
  obtain ⟨operandValues', resValues, mem', varState', hOV, hInterp', hSet, hNew⟩ := hinterp
  rw [hOpVals, Option.some.injEq] at hOV
  subst hOV
  simp only [OperationPtr.interpret] at hInterp'
  rw [hOpType] at hInterp'
  simp only [← hProps, interpretOp'] at hInterp'
  rw [hSemSrc] at hInterp'
  obtain ⟨rfl, rfl, rfl⟩ :
      resValues = #[RuntimeValue.int intType.bitwidth (srcFn x y props)] ∧
      mem' = state.memory ∧ cf = none := by grind
  subst hNew
  refine ⟨rfl, ?_, rfl⟩
  rw [VariableState.getVar?_getResult_of_setResultValues? (by rw [hNumResults]; omega) hSet]
  simp

/-- Interpreting an `llvm.mlir.constant` with integer value attribute `intAttr` and integer
    result type `intType` binds its result to the (never-poison) constant value. Applied at
    `newState := state` this unfolds the `EquationHolds` fact of a matched constant. -/
theorem constantOp_interpretOp_unfold {ctx : WfIRContext OpCode} {cstOp : OperationPtr}
    {intAttr : IntegerAttr} {intType : IntegerType} {hIsTy}
    {state newState : InterpreterState ctx} {cf} (inBounds : cstOp.InBounds ctx.raw)
    (hOpType : cstOp.getOpType! ctx.raw = .llvm .mlir__constant)
    (hNumResults : cstOp.getNumResults! ctx.raw = 1)
    (hProps : (cstOp.getProperties! ctx.raw (.llvm .mlir__constant)).value = .integer intAttr)
    (hResType : ((cstOp.getResult 0).get! ctx.raw).type = ⟨.integerType intType, hIsTy⟩)
    (hinterp : interpretOp cstOp state inBounds = some (.ok (newState, cf))) :
    newState.variables.getVar? (cstOp.getResult 0) =
      some (RuntimeValue.int intType.bitwidth
        (Data.LLVM.Int.constant intType.bitwidth intAttr.value)) := by
  rw [interpretOp_some_iff] at hinterp
  obtain ⟨operandValues, resValues, mem', varState', hOV, hInterp', hSet, hNew⟩ := hinterp
  have hResTypes0 : (cstOp.getResultTypes! ctx.raw)[0]?
      = some ⟨.integerType intType, hIsTy⟩ := by
    have hsz : (cstOp.getResultTypes! ctx.raw).size = 1 := by
      rw [OperationPtr.getResultTypes!.size_eq_getNumResults!, hNumResults]
    have helem := OperationPtr.getResultTypes!.getElem!_eq (op := cstOp) (ctx := ctx.raw)
      (index := 0) (by omega)
    rw [Array.getElem?_eq_getElem (by omega),
      show (cstOp.getResultTypes! ctx.raw)[0] = (cstOp.getResultTypes! ctx.raw)[0]! from by grind,
      helem, hResType]
  simp only [OperationPtr.interpret] at hInterp'
  rw [hOpType] at hInterp'
  simp only [interpretOp', Llvm.interpretOp', hResTypes0, hProps, pure, Interp] at hInterp'
  obtain ⟨rfl, rfl, rfl⟩ :
      resValues = #[RuntimeValue.int intType.bitwidth
        (Data.LLVM.Int.constant intType.bitwidth intAttr.value)] ∧
      mem' = state.memory ∧ cf = none := by grind
  subst hNew
  rw [VariableState.getVar?_getResult_of_setResultValues? (by rw [hNumResults]; omega) hSet]
  simp

/-! ## The packaged graph lemma for `matchNot` -/

set_option maxHeartbeats 1000000 in
/-- Semantic content of a successful `matchNot v = some y` at a program point dominated by `v`:
    in any source state satisfying `EquationLemmaAt` before `op` (with `v` an operand of `op`),
    the runtime value of `v` is `xor yv (-1)` where `yv` is the runtime value of `y`. The
    accompanying structural facts (type, dominance, in-bounds, not-a-result) are exactly what a
    `PreservesSemantics` proof needs to read `y`'s refined value in the target state. -/
theorem matchNot_getVar?_of_EquationLemmaAt {ctx : WfIRContext OpCode}
    (ctxDom : ctx.Dom) (ctxVerif : ctx.Verified)
    {op : OperationPtr} {opInBounds : op.InBounds ctx.raw}
    {state : InterpreterState ctx}
    (stateWf : state.EquationLemmaAt (InsertPoint.before op) (by grind))
    {v y : ValuePtr} {intType : IntegerType}
    (hMatch : matchNot v ctx.raw = some y)
    (hOperand : v ∈ op.getOperands! ctx.raw)
    (hVType : (v.getType! ctx.raw).val = Attribute.integerType intType) :
    ∃ yv, state.variables.getVar? y = some (RuntimeValue.int intType.bitwidth yv) ∧
      state.variables.getVar? v = some (RuntimeValue.int intType.bitwidth
        (Data.LLVM.Int.xor yv (Data.LLVM.Int.constant intType.bitwidth (-1)))) ∧
      (y.getType! ctx.raw).val = Attribute.integerType intType ∧
      y.dominatesIp (InsertPoint.before op) ctx ∧
      y.InBounds ctx.raw ∧
      y ∉ op.getResults! ctx.raw := by
  -- Syntactic facts from the match.
  obtain ⟨vPtr, cst, cstAttr, rfl, hXori, hCstMatch, hCstVal⟩ := matchNot_implies hMatch
  obtain ⟨hXorType, hXorNumResults, hXorOperands⟩ := matchXori_implies hXori
  obtain ⟨cstPtr, rfl, hCstOp⟩ := matchConstantIntVal_implies hCstMatch
  obtain ⟨hCstType, hCstProps⟩ := matchConstantIntOp_implies hCstOp
  -- In-bounds facts for the two matched defining ops.
  have hvIn : (ValuePtr.opResult vPtr).InBounds ctx.raw := by grind
  have hXorOpIn : vPtr.op.InBounds ctx.raw := by grind [OpResultPtr.InBounds]
  -- `v` is the unique result of the matched `xor`.
  have hvIdx : vPtr.index < vPtr.op.getNumResults! ctx.raw := by
    grind [OpResultPtr.inBounds_OperationPtr_getNumResults!]
  have hvEq : vPtr = vPtr.op.getResult 0 := by
    have hidx : vPtr.index = 0 := by omega
    cases vPtr
    simp only [OperationPtr.getResult, OpResultPtr.mk.injEq]
    exact ⟨trivial, hidx⟩
  -- The matched `xor` is a verified integer binop; extract its structural facts.
  have hXorVerified : vPtr.op.Verified ctx hXorOpIn := by grind
  obtain ⟨-, -, -, -, xorIntType, hXorResType, hXorOperand0Type, hXorOperand1Type⟩ :=
    OperationPtr.Verified.llvm_xor hXorVerified hXorType
  -- The binop's integer type is the type of `v`, i.e. `intType`.
  have hVTypeEq : (ValuePtr.opResult vPtr).getType! ctx.raw
      = ((vPtr.op.getResult 0).get! ctx.raw).type := by
    rw [hvEq]; rfl
  have hIntTypeEq : intType = xorIntType := by
    rw [hVTypeEq, hXorResType] at hVType
    grind
  subst hIntTypeEq
  -- Operand access: the `xor`'s operands are `y` and the constant.
  have hyIdxEq : y = (vPtr.op.getOperands! ctx.raw)[0]! := by rw [hXorOperands]; rfl
  have hCstIdxEq : ValuePtr.opResult cstPtr = (vPtr.op.getOperands! ctx.raw)[1]! := by
    rw [hXorOperands]; rfl
  have hXorOperand0 : vPtr.op.getOperand! ctx.raw 0 = y := by
    rw [hyIdxEq]
    grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hXorOperand1 : vPtr.op.getOperand! ctx.raw 1 = ValuePtr.opResult cstPtr := by
    rw [hCstIdxEq]
    grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hyType : (y.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hXorOperand0, hXorOperand0Type]
  have hCstValType : ((ValuePtr.opResult cstPtr).getType! ctx.raw).val
      = Attribute.integerType intType := by
    rw [← hXorOperand1, hXorOperand1Type]
  -- Dominance: the `xor` strictly dominates `op`, so it has been interpreted into `state`.
  have hXorDefines : (ValuePtr.opResult vPtr).getDefiningOp! ctx.raw = some vPtr.op := by
    have hOwner := (ctx.wellFormed.operations vPtr.op hXorOpIn).result_owner 0
      (by grind)
    grind [ValuePtr.getDefiningOp!]
  have hXorSDom : vPtr.op.strictlyDominates op ctx :=
    OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands! ctxDom
      hXorDefines hOperand
  have hXorDomIp : vPtr.op.dominatesIp (InsertPoint.before op) ctx := by
    grind
  have hXorPure : vPtr.op.Pure ctx.raw := OperationPtr.Pure.llvm_xor hXorType
  obtain ⟨cfX, hInterpXor⟩ := stateWf vPtr.op hXorOpIn hXorPure hXorDomIp
  -- Unfold the `xor`'s interpretation (`newState := state`).
  obtain ⟨yv, cv, hyVal, hcVal, -, hXorResVal, -⟩ :=
    matchBinaryOp_interpretOp_unfold (srcOp := .xor)
      (srcFn := fun a b _ => Data.LLVM.Int.xor a b)
      (props := vPtr.op.getProperties! ctx.raw (.llvm .xor))
      hXorOpIn hXorType hXorNumResults hXorOperands rfl
      (by intro bw a b props resultTypes blockOperands mem
          simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure])
      hInterpXor hyType hCstValType
  -- The constant's structural facts.
  have hCstIn : (ValuePtr.opResult cstPtr).InBounds ctx.raw := by
    grind [OperationPtr.getOperands!]
  have hCstOpIn : cstPtr.op.InBounds ctx.raw := by grind [OpResultPtr.InBounds]
  have hCstVerified : cstPtr.op.Verified ctx hCstOpIn := by grind
  obtain ⟨hCstNumResults, -, -, -⟩ :=
    OperationPtr.Verified.llvm_mlir__constant hCstVerified hCstType
  have hCstIdx : cstPtr.index < cstPtr.op.getNumResults! ctx.raw := by
    grind [OpResultPtr.inBounds_OperationPtr_getNumResults!]
  have hCstEq : cstPtr = cstPtr.op.getResult 0 := by
    have hidx : cstPtr.index = 0 := by omega
    cases cstPtr
    simp only [OperationPtr.getResult, OpResultPtr.mk.injEq]
    exact ⟨trivial, hidx⟩
  have hCstResType : ((cstPtr.op.getResult 0).get! ctx.raw).type
      = ⟨.integerType intType, by grind⟩ := by
    have : ((ValuePtr.opResult cstPtr).getType! ctx.raw)
        = ((cstPtr.op.getResult 0).get! ctx.raw).type := by
      rw [hCstEq]; rfl
    grind [Subtype.ext]
  -- Dominance: the constant strictly dominates the `xor`, hence `op` (transitivity).
  have hCstDefines : (ValuePtr.opResult cstPtr).getDefiningOp! ctx.raw = some cstPtr.op := by
    have hOwner := (ctx.wellFormed.operations cstPtr.op hCstOpIn).result_owner 0
      (by grind)
    grind [ValuePtr.getDefiningOp!]
  have hCstSDomXor : cstPtr.op.strictlyDominates vPtr.op ctx :=
    OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands! ctxDom
      hCstDefines (by grind [OperationPtr.getOperands!])
  have hCstSDom : cstPtr.op.strictlyDominates op ctx :=
    OperationPtr.strictlyDominates_trans hCstSDomXor hXorSDom
  have hCstDomIp : cstPtr.op.dominatesIp (InsertPoint.before op) ctx := by
    grind
  have hCstPure : cstPtr.op.Pure ctx.raw := OperationPtr.Pure.llvm_mlir__constant hCstType
  obtain ⟨cfC, hInterpCst⟩ := stateWf cstPtr.op hCstOpIn hCstPure hCstDomIp
  -- Unfold the constant's interpretation: its result is the non-poison `-1`.
  have hCstResVal :=
    constantOp_interpretOp_unfold hCstOpIn hCstType hCstNumResults hCstProps hCstResType
      hInterpCst
  -- The two reads of the constant's value agree, pinning `cv`.
  have hcvEq : cv = Data.LLVM.Int.constant intType.bitwidth cstAttr.value := by
    rw [hCstEq] at hcVal
    grind
  -- Assemble.
  refine ⟨yv, hyVal, ?_, hyType, ?_, ?_, ?_⟩
  · rw [hvEq, hXorResVal, hcvEq, hCstVal]
  · exact ValuePtr.dominatesIp_before_of_strictlyDominates
      (ctxDom.operand_dominates_op hXorOpIn (by grind [OperationPtr.getOperands!])) hXorSDom
  · grind [OperationPtr.getOperands!]
  · exact IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom
      (OperationPtr.dominates_of_strictlyDominates hXorSDom) y
      (by grind [OperationPtr.getOperands!])

end Veir
